import MinHS.Parse
import MinHS.Syntax
import MinHS.TypeChecker
import MinHS.Pretty
import MinHS.Evaluator
import Control.Monad
import Data.Either
import Data.Monoid((<>))
import Options.Applicative.Types
import Options.Applicative
import Text.PrettyPrint.ANSI.Leijen (Pretty (..),Doc, putDoc, plain)

type Action a b = a -> Either (IO ()) b

main = execParser argsInfo >>= main'
  where main' (pipeline, filter, file) = (pipeline filter <$> readFile file) >>= either id id

        argsInfo = info (helper <*> args)
                    (fullDesc <> progDesc "A interpreter for a small functional language"
                              <> header "MinHS - COMP3161 Concepts of Programming Languages")

        args =  (,,) <$> option readAction ( long "dump"
                               <> metavar "STAGE"
                               <> value (evaluatorAction)
                               <> help "stage after which to dump the current state. \n                           [parser,parser-raw,typechecker,evaluator]")
                     <*> flag id plain (long "no-colour"
                                     <> help "do not use colour when pretty printing")
                     <*> argument str (metavar "FILE")

        readAction :: ReadM ((Doc -> Doc) -> Action String (IO ()))
        readAction = readerAsk >>= \x -> case x of
            "parser"      -> return $ \f -> parser >=> printer f
            "parser-raw"  -> return $ \f -> parser >=> rawPrinter
            "typechecker" -> return $ \f -> parser >=> typechecker f >=> printer f
            "evaluator"   -> return $ evaluatorAction
            _             -> readerAbort (ShowHelpText Nothing)
        evaluatorAction :: (Doc -> Doc) -> Action String (IO ())
        evaluatorAction f = parser >=> typechecker f >=> evaluator >=> printer f

        parser :: Action String Program
        parser = either (Left . putStrLn . show) Right . parseProgram ""

        typechecker :: (Doc -> Doc) -> Action Program Program
        typechecker f p | Just v <- typecheck p = Left . (>> putStrLn "") . putDoc . f . pretty $ v
                        | otherwise             = Right $ p

        evaluator p = Right $ evaluate p

        rawPrinter :: (Show a) => Action a (IO ())
        rawPrinter = Right . putStrLn . show

        printer :: (Pretty a) => (Doc -> Doc) -> Action a (IO ())
        printer filter = Right . (>> putStrLn "") . putDoc . filter . pretty

        fromRight = either (error "fromRight on Left") id
