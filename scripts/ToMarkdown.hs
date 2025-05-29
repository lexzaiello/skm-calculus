import Text.Printf (printf)
import System.IO
import System.Environment

toMarkdown :: String -> String
toMarkdown = unlines . snd . foldl step (False, ([] :: [String])) . lines
  where
    step (isLean, acc) line
      | take 3 line == "--/" = (True, acc ++ ["```lean", drop 3 line])
      | take 3 line == "/--" = (False, acc ++ [drop 3 line, "```"])
      | otherwise            = (isLean, acc ++ [line])

main :: IO ()
main = getArgs >>= (\a -> case a of
    pat:_ -> readFile pat >>= (\cts -> putStrLn $ toMarkdown cts)
    [] -> hPutStrLn stderr "Please input a file to generate markdown for.")
