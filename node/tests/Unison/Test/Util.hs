{-# Language OverloadedStrings #-}

module Unison.Test.Util where

import Control.Applicative
import Data.Text.Encoding (decodeUtf8)
import Unison.Hash (Hash)
import Unison.Codebase (Codebase)
import Unison.Note (Noted)
import Unison.Reference (Reference)
import Unison.Runtime.Address
import Unison.Symbol (Symbol)
import Unison.Term (Term)
import Unison.Type (Type)
import Unison.Var (Var)
import qualified Data.ByteString as B
import qualified Data.Text as Text
import qualified Data.Text.IO as Text.IO
import qualified System.FilePath as FP
import qualified Unison.ABT as ABT
import qualified Unison.BlockStore.MemBlockStore as MBS
import qualified Unison.Builtin as Builtin
import qualified Unison.Codebase as Codebase
import qualified Unison.Cryptography as C
import qualified Unison.Hash as Hash
import qualified Unison.Codebase.FileStore as FS
import qualified Unison.Codebase.BlockStoreStore as BSS
import qualified Unison.Note as Note
import qualified Unison.Parsers as Parsers
import qualified Unison.Reference as R
import qualified Unison.Reference as Reference
import qualified Unison.Runtime.ExtraBuiltins as EB
import qualified Unison.Term as Term
import qualified Unison.View as View
import qualified Unison.Util.Logger as L

type DFO = View.DFO
type V = Symbol DFO
type TermV = Term V
type TestCodebase = Codebase IO V R.Reference (Type V) (Term V)

hash :: Var v => Term.Term v -> Reference
hash (Term.Ref' r) = r
hash t = Reference.Derived (ABT.hash t)

makeRandomAddress :: C.Cryptography k syk sk skp s h c -> IO Address
makeRandomAddress crypt = Address <$> C.randomBytes crypt 64

loadDeclarations :: L.Logger -> FilePath -> Codebase IO V Reference (Type V) (Term V) -> IO ()
loadDeclarations logger path codebase = do
  -- note - when run from repl current directory is root, but when run via stack test, current
  -- directory is the shared subdir - so we check both locations
  txt <- decodeUtf8 <$> (B.readFile path <|> B.readFile (".." `FP.combine` path))
  let str = Text.unpack txt
  _ <- Note.run $ Codebase.declare' Term.ref str codebase
  L.info logger $ "loaded file: " ++ path

makeTestCodebase :: IO (TestCodebase, String -> Term V, Term V -> Noted IO (Term V))
makeTestCodebase = do
  logger <- L.atomic (L.atInfo L.toStandardOut)
  let crypto = C.noop "dummypublickey"
  putStrLn "creating block store..."
  blockStore <- MBS.make' (makeRandomAddress crypto) makeAddress
  putStrLn "created block store, creating Codebase store..."
  store' <- BSS.make blockStore
  -- store' <- FS.make "blockstore.file"
  putStrLn "created Codebase store..., building extra builtins"
  extraBuiltins <- EB.make logger blockStore crypto
  putStrLn "extra builtins created"
  codebase <- pure $ Codebase.make hash store'
  let builtins = Builtin.make logger ++ extraBuiltins
  Codebase.addBuiltins builtins store' codebase
  let eval = Codebase.interpreter builtins codebase
  L.info logger "Codebase created"
  loadDeclarations logger "unison-src/base.u" codebase
  loadDeclarations logger "unison-src/extra.u" codebase
  builtins <- Note.run $ Codebase.allTermsByVarName Term.ref codebase
  let parse = Parsers.bindBuiltins builtins [] . Parsers.unsafeParseTerm
  pure (codebase, parse, eval)
