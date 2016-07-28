{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecursiveDo #-}

module Unison.Runtime.VM where

import Data.Semigroup
import Data.List
import GHC.Generics
import Unison.Term (Term)
import Unison.Var (Var)
import qualified Unison.Term as T
import Unison.Reference (Reference)
import Unison.Runtime.Vector (Vector)
import qualified Unison.Runtime.Vector as Vector
import Data.Foldable
import qualified Data.Text as Text

newtype Program v builtin = Program [Slot (Program v) v builtin] deriving (Show,Generic)

type PureFn p v b = Stack p v b -> Stack p v b
type ImpureFn p v b = Stack p v b -> IO (Stack p v b)

data Stack p v builtin
  = Empty
  | Cons !(Value p v builtin) !(Stack p v builtin) deriving (Show,Generic)

data Value p v builtin
  = Double !Double
  | Text !Text.Text
  | Var !(Maybe v)
  | Vector !(Vector (Value p v builtin))
  | Suspend !(p builtin) -- todo: [v] track variable names to use for decompile
  | Builtin builtin
  | Frame
  deriving (Show,Generic)

data Slot p v builtin
  = Value (Value p v builtin)
  | Dup !Int -- Dup 0 duplicates top of stack
  | Ap
  | Return
  | LetRec [Slot p v builtin] (Slot p v builtin)
  deriving (Show,Generic)

at :: Int -> Stack p v b -> Value p v b
at _ _ = error "todo - revisit"

interpret :: (builtin -> Either (ImpureFn (Program v) v builtin) (PureFn (Program v) v builtin))
          -> Program v builtin
          -> IO (Stack (Program v) v builtin)
interpret c prog = interpret' c prog Empty

interpret' :: (builtin -> Either (ImpureFn (Program v) v builtin) (PureFn (Program v) v builtin))
           -> Program v builtin
           -> Stack (Program v) v builtin
           -> IO (Stack (Program v) v builtin)
interpret' c (Program prog) stack = go prog stack where
  go (Dup 0 : prog) stack@(Cons top _) = go prog (Cons top (Cons top stack))
  go (Dup n : prog) stack = go prog (Cons (at n stack) stack)
  go (Ap : prog) (Cons (Builtin f) stack) = case c f of
    Left impure -> go prog =<< impure stack
    Right pure -> go prog (pure stack)
  go (Ap : prog) (Cons (Suspend (Program f)) stack) = go (f ++ prog) stack
  go (Return : prog) Empty = go prog Empty
  go (Return : prog) (Cons top bot) = go prog (dropToFrame [] bot) where
    finish [] bot = Cons top bot
    finish acc bot = Cons (Suspend (Program (Value top : acc))) bot
    dropToFrame acc Empty = finish acc Empty
    dropToFrame acc (Cons Frame bot) = finish acc bot
    dropToFrame acc (Cons top bot) = dropToFrame (Value top : acc) bot
  go (LetRec [binding] body : prog) stack = mdo
    stack'@(Cons result _) <- go (binding : prog) (Cons result stack)
    go (body : Ap : prog) stack'
  -- try generalizing this to two bindings, etc
  go (Value v : prog) stack = go prog (Cons v stack)
  go [] stack = pure stack
  go (Ap : _) _ = error "Ap requires a function at top of stack"

newtype Builder v b = Builder (Program v b -> Program v b)

build :: Builder v b -> Program v b
build (Builder b) = b (Program [])

instance Monoid (Builder v b) where
  mempty = Builder id
  Builder f `mappend` Builder g = Builder (f . g)

instance Semigroup (Builder v b) where
  (<>) = mappend

push :: Slot (Program v) v b -> Builder v b
push slot = Builder $ \(Program p) -> Program (slot:p)

program :: [Slot (Program v) v b] -> Program v b
program slots = Program slots

compile :: Var v => Term v -> Program v Reference
compile = build . compile'

compile' :: Var v => Term v -> Builder v Reference
compile' t = go [] t where
  go vs t = case t of
    T.Blank' -> push (Value $ Var Nothing)
    T.Ref' r -> push (Value $ Builtin r)
    T.Lit' l -> case l of
      T.Number n -> push (Value $ Double n)
      T.Text txt -> push (Value $ Text txt)
    T.Ann' x _ -> go vs x
    -- todo: strictly evaluate elements
    T.Vector' xs -> push (Value $ Vector (Vector.fromList $ map (Suspend . build . go vs) (toList xs)))
    T.App' f x -> go vs x <> go vs f <> push Ap
    T.Var' v -> case elemIndex v vs of
      Just i -> push (Dup i)
      Nothing -> push (Value $ Var (Just v))
    T.LamNamed' v body -> push (Value $ Suspend (build (push (Value Frame) <> go (v:vs) body <> push Return)))
    T.Let1Named' v b body ->
      push (Value Frame) <> go vs b <> go (v:vs) body <> push Return
    T.LetRecNamed' bs body -> push (LetRec bs' body') where
      vs' = reverse (map fst bs) ++ vs
      bs' = [ Value $ Suspend (build (push (Value Frame) <> go vs' b <> push Return)) | (_,b) <- bs ]
      body' = Value . Suspend $ build (go vs' body <> push Return)
