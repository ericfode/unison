{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE RecursiveDo #-}

module Unison.Runtime.VM where

import Data.Foldable
import Data.List
import Data.Semigroup
import GHC.Generics
import Unison.Reference (Reference)
import Unison.Runtime.Vector (Vector)
import Unison.Term (Term)
import Unison.Var (Var)
import qualified Data.Text as Text
import qualified Data.Vector as DV
import qualified Unison.Reference as R
import qualified Unison.Runtime.Vector as Vector
import qualified Unison.Term as T

newtype Program v builtin = Program [Instruction (Value (Program v) v builtin)] deriving (Show,Generic)

type PureFn p v b = Machine p v b -> Machine p v b
type ImpureFn p v b = Machine p v b -> IO (Machine p v b)

type Stack p v builtin = DV.Vector (Value p v builtin)

data Machine p v builtin
  = Frame !(Stack p v builtin) !(Stack p v builtin) !(Maybe (Machine p v builtin))

data Fn p builtin
  = Builtin builtin
  | Lam (p builtin) deriving Show

data Value p v builtin
  = Double !Double
  | Text !Text.Text
  | Var !(Maybe v)
  | Vector !(Vector (Value p v builtin))
  | Closure !Int !(Stack p v builtin) !(Fn p builtin) -- todo: [v] track variable names to use for decompile
  deriving (Show,Generic)

data Instruction v
  = Push !v
  | Local !Int -- Push local variable onto work stack
  | Call -- Call function at top of work stack, move work stack to local variable stack
  | Return -- Reify work stack as a value, push it onto work stack of below frame, pop frame
  | LetRec [v] [Instruction v]
  deriving (Show,Generic,Functor,Traversable,Foldable)

at :: Int -> Machine p v b -> Value p v b
at n (Frame args _ bot) | n < DV.length args = case args DV.!? (DV.length args - 1 - n) of
  Just v -> v
  Nothing -> case bot of
    Nothing -> error "invalid index"
    Just f -> at (n - DV.length args) f

zero :: Machine p v b
zero = Frame DV.empty DV.empty Nothing

traceInterpret
  :: (Show builtin, Show v)
  => (builtin -> Either (ImpureFn (Program v) v builtin) (PureFn (Program v) v builtin))
  -> [Instruction (Value (Program v) v builtin)]
  -> IO (Machine (Program v) v builtin)
traceInterpret c prog = interpret' c (Just trace) prog zero where
  trace i m = do
    putStrLn (show i)
    putStrLn (debugMachine m)

interpret' :: (builtin -> Either (ImpureFn (Program v) v builtin) (PureFn (Program v) v builtin))
           -> Maybe (Instruction (Value (Program v) v builtin) -> Machine (Program v) v builtin -> IO ())
           -> [Instruction (Value (Program v) v builtin)]
           -> Machine (Program v) v builtin
           -> IO (Machine (Program v) v builtin)
interpret' c trace prog machine = go0 prog machine where
  go0 = case trace of
    Nothing -> go
    Just trace -> \p m -> case p of
      [] -> go p m
      h : _ -> trace h m >> go p m
  go (Local n : prog) m@(Frame args work bot) = go0 prog (Frame args (work `DV.snoc` at n m) bot)
  go (Push v : prog)    (Frame args work bot) = go0 prog (Frame args (work `DV.snoc` v) bot)
  go (Call : prog) m@(Frame args provided bot) | DV.length provided >= 1 = case DV.unsafeLast provided of
    Closure nRequired env fn
      | nargs == nRequired -> case fn of -- nargs counts the closure itself, whereas nRequired doesn't
        Builtin fn -> case c fn of
          Left impure -> go0 prog =<< impure m
          Right pure -> go0 prog (pure m)
        Lam (Program fn) -> go0 (fn ++ prog) (Frame args' DV.empty bot') where
          args' = DV.concat [env, DV.init provided]
          bot' = Just (Frame args DV.empty bot)
      | nargs > nRequired -> -- over-application, like `id id 42`
        let
          provided' = DV.take nRequired provided
          extra = Push <$> DV.toList (DV.drop nRequired provided)
        in go0 ((Call : extra) ++ prog) (Frame args (provided' `DV.snoc` Closure nRequired env fn) bot)
      | nargs < nRequired ->  -- under-application `(+) 1`
        go0 prog (Frame args (DV.singleton $ Closure (nRequired-nargs) (DV.concat[env,provided]) fn) bot)
    _ -> error "attempt to apply non-function"
    where nargs = DV.length provided - 1 -- don't include the Closure itself, only the arguments to it
  go [] stack = pure stack
  go (Return : prog) (Frame _ work bot) = case maybe zero id bot of
    Frame args work2 bot -> go0 prog (Frame args (DV.concat [work2,work]) bot)
  --go (LetRec [binding] body : prog) m =
  --  let binding' = Suspend . Program $ [Push binding, Push binding, Call, Return]
  --  -- body can refer to itself via Local 0
  --  in go0 (Push binding' : (Push . Suspend . Program $ body) : Call : Return : prog) m
  --  -- generalize this to two bindings, etc
  --go _ Bottom = error "Bottom machine state"
  go (Call : _) _ = error "Call on Empty work stack"

newtype Builder v = Builder ([Instruction v] -> [Instruction v])

build :: Builder v -> [Instruction v]
build (Builder b) = b []

instance Monoid (Builder v) where
  mempty = Builder id
  Builder f `mappend` Builder g = Builder (f . g)

instance Semigroup (Builder v) where
  (<>) = mappend

one :: Instruction v -> Builder v
one slot = Builder (slot:)

thunk :: [Instruction (Value (Program v1) v1 builtin)] -> Value (Program v1) v builtin
thunk = Closure 0 DV.empty . Lam . Program

compile :: Var v => Term v -> [Instruction (Value (Program v) v Reference)]
compile = build . compile'

compile' :: Var v => Term v -> Builder (Value (Program v) v Reference)
compile' t = go [] t where
  go vs t = case t of
    T.Blank' -> one (Push $ Var Nothing)
    T.Ref' r -> one (Push . Closure 0 DV.empty . Builtin $ r)
    T.Lit' l -> case l of
      T.Number n -> one (Push $ Double n)
      T.Text txt -> one (Push $ Text txt)
    T.Ann' x _ -> go vs x
    -- todo: strictly evaluate elements
    T.Vector' xs -> one (Push $ Vector (Vector.fromList $ map (thunk . build . go vs) (toList xs)))
    T.Apps' f args -> mconcat [ go vs x | x <- args ] <> go vs f <> one Call
    T.Var' v -> case elemIndex v vs of
      Just i -> one (Local i)
      Nothing -> one (Push $ Var (Just v))
    T.LamsNamed' args body -> one (Push . Closure (length args) DV.empty . Lam . Program $ (build (go (reverse args ++ vs) body <> one Return)))
    T.Let1Named' v b body -> go vs b
                          <> one (Push . thunk $ (build (go (v:vs) body <> one Return)))
                          <> one Call
    T.LetRecNamed' bs body -> one (LetRec bs' body') where
      vs' = reverse (map fst bs) ++ vs
      bs' = [ thunk $ (build (go vs' b <> one Return)) | (_,b) <- bs ]
      body' = build (go vs' body)
    _ -> error $ "do not know how to compile: " ++ show t

{-
builtins ref = case ref of
  R.Derived _ -> error "no go"
  R.Builtin r -> case Text.unpack r of
    "Number.plus" -> Right $ \(Frame args (Cons self (Cons y (Cons x tl))) bot) -> case (x, y) of
      (Double x, Double y) -> Frame args (Cons (Double (x+y)) tl) bot
      _ -> Frame args (Cons (Suspend (Program [Push x, Push y, Push self, Call])) tl) bot
    "Number.minus" -> Right $ \(Frame args (Cons self (Cons y (Cons x tl))) bot) -> case (x, y) of
      (Double x, Double y) -> Frame args (Cons (Double (x-y)) tl) bot
      _ -> Frame args (Cons (Suspend (Program [Push x, Push y, Push self, Call])) tl) bot
    r -> error $ "unknown ref " ++ r

-}

debugMachine :: (Show v, Show b) => Machine (Program v) v b -> String
debugMachine (Frame args work bot) =
  show args ++ " " ++ show work ++ "\n" ++
  (maybe "" debugMachine bot)
