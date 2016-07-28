{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE RecursiveDo #-}

module Unison.Runtime.VM where

import Data.Semigroup
import Data.List
import GHC.Generics
import Unison.Term (Term)
import Unison.Var (Var)
import qualified Unison.Term as T
import Unison.Reference (Reference)
import qualified Unison.Reference as R
import Unison.Runtime.Vector (Vector)
import qualified Unison.Runtime.Vector as Vector
import Data.Foldable
import qualified Data.Text as Text

newtype Program v builtin = Program [Instruction (Value (Program v) v builtin)] deriving (Show,Generic)

type PureFn p v b = Machine p v b -> Machine p v b
type ImpureFn p v b = Machine p v b -> IO (Machine p v b)

data Stack p v builtin
  = Empty
  | Cons !(Value p v builtin) !(Stack p v builtin)

data Machine p v builtin
  = Bottom
  | Frame !(Stack p v builtin) !(Stack p v builtin) !(Machine p v builtin)

data Value p v builtin
  = Double !Double
  | Text !Text.Text
  | Var !(Maybe v)
  | Vector !(Vector (Value p v builtin))
  | Suspend !(p builtin) -- todo: [v] track variable names to use for decompile
  | Builtin builtin
  deriving (Show,Generic)

data Instruction v
  = Push !v
  | Local !Int -- Push local variable onto work stack
  | Call -- Call function at top of work stack, move work stack to local variable stack
  | Return -- Reify work stack as a value, push it onto work stack of below frame, pop frame
  | LetRec [v] [Instruction v]
  deriving (Show,Generic,Functor,Traversable,Foldable)

at :: Int -> Machine p v b -> Value p v b
at n (Frame args _ bot) = go n args bot where
  go 0 (Cons h _) _ = h
  go n (Cons _ t) bot = go (n-1) t bot
  go n Empty (Frame args _ bot) = go n args bot
  go _ Empty Bottom = error "invalid index"
at _ Bottom = error "invalid index"

traceInterpret
  :: (Show builtin, Show v)
  => (builtin -> Either (ImpureFn (Program v) v builtin) (PureFn (Program v) v builtin))
  -> [Instruction (Value (Program v) v builtin)]
  -> IO (Machine (Program v) v builtin)
traceInterpret c prog = interpret' c (Just trace) prog Bottom where
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
    Nothing -> \p m -> go p m
    Just trace -> \p m -> case p of
      [] -> go p m
      h : _ -> trace h m >> go p m
  go (Local n : prog) m@(Frame args work bot) = go0 prog (Frame args (Cons (at n m) work) bot)
  go (Return : prog) machine = case machine of
    Frame _ work bot -> case bot of
      Bottom -> go0 prog (Frame Empty (transfer work Empty) Bottom)
      Frame args work2 bot -> go0 prog (Frame args (transfer work work2) bot)
    _ -> error "cannot return to null caller"
  go (Push v : prog) m = case m of
    Frame args work bot -> go0 prog (Frame args (Cons v work) bot)
    Bottom -> go0 prog (Frame Empty (Cons v Empty) Bottom)
  go (Call : prog) m@(Frame args (Cons fn work) bot) = call fn where
    call (Builtin f) = case c f of
      Left impure -> go0 prog =<< impure m
      Right pure -> go0 prog (pure m)
    call (Suspend (Program instructions)) = go0 (instructions ++ prog) frame' where
      frame' = case prog of
        Return : _ -> Frame work Empty bot -- proper tail calls: recycle current frame
        _ -> Frame work Empty (Frame args Empty bot)
    call _ = case work of
      Empty -> go0 prog m
      _ -> error "call with non-function in head position"
  go (LetRec [binding] body : prog) m =
    let binding' = Suspend . Program $ [Push binding, Push binding, Call, Return]
    -- body can refer to itself via Local 0
    in go0 (Push binding' : (Push . Suspend . Program $ body) : Call : Return : prog) m
    -- generalize this to two bindings, etc
  go [] stack = pure stack
  go _ Bottom = error "Bottom machine state"
  go (Call : _) _ = error "Call on Empty work stack"

-- | Push elements of first stack onto second stack
transfer :: Stack p v builtin -> Stack p v builtin -> Stack p v builtin
transfer (Cons h Empty) s2 = Cons h s2
transfer (Cons h t) s2 = transfer t (Cons h s2)
transfer Empty s2 = s2

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

compile :: Var v => Term v -> [Instruction (Value (Program v) v Reference)]
compile = build . compile'

compile' :: Var v => Term v -> Builder (Value (Program v) v Reference)
compile' t = go [] t where
  go vs t = case t of
    T.Blank' -> one (Push $ Var Nothing)
    T.Ref' r -> one (Push $ Builtin r)
    T.Lit' l -> case l of
      T.Number n -> one (Push $ Double n)
      T.Text txt -> one (Push $ Text txt)
    T.Ann' x _ -> go vs x
    -- todo: strictly evaluate elements
    T.Vector' xs -> one (Push $ Vector (Vector.fromList $ map (Suspend . Program . build . go vs) (toList xs)))
    T.Apps' f args -> mconcat [ go vs x | x <- args ] <> go vs f <> one Call
    T.Var' v -> case elemIndex v vs of
      Just i -> one (Local i)
      Nothing -> one (Push $ Var (Just v))
    T.LamsNamed' args body -> one (Push . Suspend . Program $ (build (go (reverse args ++ vs) body <> one Return)))
    T.Let1Named' v b body -> go vs b
                          <> one (Push . Suspend . Program $ (build (go (v:vs) body <> one Return)))
                          <> one Call
    T.LetRecNamed' bs body -> one (LetRec bs' body') where
      vs' = reverse (map fst bs) ++ vs
      bs' = [ Suspend . Program $ (build (go vs' b <> one Return)) | (_,b) <- bs ]
      body' = build (go vs' body)
    _ -> error $ "do not know how to compile: " ++ show t

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

stackToList :: Stack p v builtin -> [Value p v builtin]
stackToList Empty = []
stackToList (Cons h t) = h : stackToList t

debugMachine :: (Show v, Show b) => Machine (Program v) v b -> String
debugMachine Bottom = ""
debugMachine (Frame args work bot) =
  show (stackToList args) ++ " " ++ show (stackToList work) ++ "\n" ++
  debugMachine bot
