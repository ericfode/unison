{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}

module Unison.Runtime.VM where

import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.IORef
import Data.List
import Unison.Reference (Reference)
import Unison.Runtime.Vector (Vector)
import Unison.Term (Term)
import Unison.Var (Var)
import qualified Data.Text as Text
import qualified Data.Vector as DV
import qualified Data.Vector.Mutable as MV
import qualified Unison.Reference as R
import qualified Unison.Runtime.Vector as Vector
import qualified Unison.Term as T

data Val v
  = Number !Double
  | Text !Text.Text
  | Symbol !(Maybe v)
  | Vector !(Vector (Val v))
  | Fn { arity :: !Int, relfect :: Program v (T.Term v), env :: !(Program v Int), invoke :: !(Program v ()) }

type Program v a = ReaderT (Stack (Val v)) IO a

data Stack a =
  Stack { topIndex :: IORef Int
        , values :: IORef (MV.IOVector a)
        , clearValue :: a }

{-
stack0 :: IO (Stack (Val v))
stack0 = do
  i <- newIORef 0
  v <- MV.new 128
  values
-}

top :: Program v (Val v)
top = ask >>= \s -> liftIO $ top' s

push :: Val v -> Program v ()
push v = ask >>= \s -> liftIO $ push' s v

pop :: Program v (Val v)
pop = ask >>= \s -> liftIO $ pop' s

popFrame' :: Int -> Program v (Val v)
popFrame' args = popFrame args >> pop

-- Saves the top element of the stack, drops the number of arguments from the
-- stack, then repushes the top element; popFrame 2 [a,b,c,d] == [a,d]
popFrame :: Int -> Program v ()
popFrame args = do
  s <- ask
  top <- liftIO $ pop' s
  liftIO $ drop' args s
  liftIO $ push' s top

at :: Int -> Program v (Val v)
at i = ask >>= \s -> liftIO $ at' i s

top' :: Stack a -> IO a
top' (Stack i vs _) = do
  i <- readIORef i
  vs <- readIORef vs
  MV.read vs i

at' :: Int -> Stack a -> IO a
at' j (Stack i vs _) = do
  i <- readIORef i
  vs <- readIORef vs
  MV.read vs (i-j)

push' :: Stack a -> a -> IO ()
push' s@(Stack ir vsr _) !a = do
  i <- readIORef ir
  vs <- readIORef vsr
  case i >= MV.length vs - 1 of
    False -> let !i' = i+1 in MV.write vs i' a >> writeIORef ir i'
    True -> do
      vs <- MV.grow vs (MV.length vs)
      writeIORef vsr vs
      push' s a

pop' :: Stack a -> IO a
pop' (Stack ir vsr null) = do
  i <- readIORef ir
  vs <- readIORef vsr
  a <- MV.read vs i
  MV.write vs i null
  let !i' = (i - 1) `max` 0
  writeIORef ir i'
  pure a

drop' :: Int -> Stack a -> IO ()
drop' n (Stack ir vsr null) = do
  i <- readIORef ir
  vs <- readIORef vsr
  MV.write vs i null
  let !i' = (i - n) `max` 0
  writeIORef ir i'

compile' :: Var v => (R.Reference -> Program v ()) -> Term v -> Program v ()
compile' link t = go [] t where
  go vs t = case t of
    T.Blank' -> push (Symbol Nothing)
    T.Lit' l -> case l of
      T.Number n -> push (Number n)
      T.Text txt -> push (Text txt)
    T.Ref' r -> link r
    T.Ann' x _ -> go vs x
    T.Var' v -> case elemIndex v vs of
      Just i -> at i >>= push
      Nothing -> push (Symbol (Just v))
    T.Vector' xs ->
      let !xs' = fmap (\x -> go vs x >> pop) (Vector.fromList . DV.toList $ xs)
      in do
        xs <- sequenceA xs'
        push $ Vector xs
    T.Let1Named' v b body -> do b'; body'; popFrame 1 where
      !b' = go vs b
      !body' = go (v:vs) body
    T.LamsNamed' args body -> push fn where
      !body' = go (reverse args ++ vs) body
      !arity = length args
      !fn = Fn arity (pure (T.lam'' args body)) (pure 0) body'
    T.LetRecNamed' bs body ->
      let
        !vs' = reverse (map fst bs) ++ vs
        !n = length bs
        !bs' = [go vs' b >> popFrame' n | (_,b) <- bs]
        !body' = go vs' body
      in mdo
        results <- forM bs' (\b -> mapM_ push results >> b)
        mapM_ push results
        body'
        popFrame n
    -- T.Apps' (T.LamsNamed' argnames body) args -- todo: give optimized impl?
    T.Apps' f args ->
      let
        !ef = eval vs f
        !eargs = forM_ args (go vs)
        !nargs = length args
        dargs = DV.map (eval vs) (DV.fromList args)
        deoptimized = do f <- ef; applied <- foldM app f (DV.toList dargs); push applied where
          app (Fn arity reify env invoke) arg = arg >>= \arg ->
            if arity == 1 then do n <- env; push arg; invoke; popFrame (n+1); pop
            else pure (Fn (arity-1) (reify2 arg) ((1+) <$> (env <* push arg)) invoke)
            where
            reify2 arg = do
              f <- reify
              arg <- decompile arg
              pure $ T.app f arg
          app _ _ = error $ "application of non-function"
      in do
        Fn arity reify env prog <- ef
        case nargs of
          _ | nargs == arity -> env >>= \n -> eargs >> prog >> popFrame (nargs+n) -- fully saturated call
            | nargs > arity -> deoptimized -- over-application, ex: id id 42
            | otherwise -> do -- nargs < arity, under-application, need to form a closure
                -- Example: let f x y z = x - y - z; g = f 12 2 in g 1 -- should be 9
                eargs -- evaluate the args
                env' <- reverse <$> replicateM nargs pop -- extract the environment
                -- create the closure from the argument
                push (Fn (arity-nargs) (reify2 env') ((+) <$> env <*> (nargs <$ forM_ env' push)) prog)
                where
                reify2 env' = do
                  f <- reify
                  args <- mapM decompile env'
                  pure $ T.apps f args
    _ -> error $ "don't know what to do with: " ++ show t
  eval vs t = go vs t >> pop

decompile :: Ord v => Val v -> Program v (T.Term v)
decompile val = case val of
  Number n -> pure $ T.num n
  Text txt -> pure $ T.text txt
  Symbol Nothing -> pure $ T.blank
  Symbol (Just v) -> pure $ T.var v
  Vector vals -> T.vector . Vector.toList <$> traverse decompile vals
  Fn _ decompile _ _ -> decompile

popDecompile :: Ord v => Program v (T.Term v)
popDecompile = decompile =<< pop

builtins :: Ord v => R.Reference -> Program v ()
builtins =
  let
    plus' = do Number x <- at 1; Number y <- at 0; push (Number (x+y))
    minus' = do Number x <- at 1; Number y <- at 0; push (Number (x-y))
    f2 r prog = Fn 2 (pure (T.ref r)) (pure 0) prog
    plus = f2 (R.Builtin "Number.plus") plus'
    minus = f2 (R.Builtin "Number.minus") minus'
  in \ref -> case ref of
    R.Derived _ -> error "no go"
    R.Builtin r -> case Text.unpack r of
      "Number.plus" -> push plus
      "Number.minus" -> push minus
      _ -> error "unknown"
