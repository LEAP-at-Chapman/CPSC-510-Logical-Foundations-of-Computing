-- Haskell version - has a runtime bug!
import Data.List (transpose)

-- Matrix type (just a list of lists)
type Matrix a = [[a]]

-- Matrix multiplication
matMul :: Num a => Matrix a -> Matrix a -> Matrix a
matMul a b = [[sum $ zipWith (*) ar bc | bc <- transpose b] | ar <- a]

-- Get nth column of a matrix
getColumn :: Int -> Matrix a -> [a]
getColumn n = map (!! n)  -- Bug: what if n >= width?

--  average of a column
averageColumn :: Int -> Matrix Double -> Double
averageColumn n mat =
    let col = getColumn n mat
        len = length col
    in sum col / fromIntegral len  -- Bug: what if matrix is empty?

-- Example usage
main :: IO ()
main = do
    let matrix1 = [[1, 2, 3],
                   [4, 5, 6]]

    -- This works fine
    print $ averageColumn 1 matrix1  -- 3.5

    -- Runtime error! Division by zero
    let emptyMatrix = [] :: Matrix Double
    print $ averageColumn 0 emptyMatrix  -- NaN (not a number due to division by zero)

    -- Runtime error! Index out of bounds
    print $ averageColumn 5 matrix1  -- Error: index too large
