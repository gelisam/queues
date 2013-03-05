{-# LANGUAGE GADTs, DeriveFunctor, Rank2Types #-}

import Data.IORef
import Data.STRef
import Data.StateVar
import Control.Monad
import Control.Monad.ST


data StateOp s a where
  Ignore :: a -> StateOp s a
  Read :: (s -> a) -> StateOp s a
  Write :: s -> StateOp s ()

stateValue :: s -> StateOp s a -> a
stateValue _ (Ignore x) = x
stateValue s (Read f) = f s
stateValue _ (Write _) = ()

newState :: s -> StateOp s a -> s
newState _ (Write x) = x
newState s _ = s


data Program op a where
  Done :: a -> Program op a
  AndThen :: op a
          -> (a -> Program op b)
          -> Program op b

evalStateProgram :: s -> Program (StateOp s) a -> a
evalStateProgram s (Done x) = x
evalStateProgram s (AndThen (Ignore x) cc) = evalStateProgram s $ cc x
evalStateProgram s (AndThen (Read f) cc) = evalStateProgram s $ cc $ f s
evalStateProgram _ (AndThen (Write s) cc) = evalStateProgram s $ cc ()


fibs :: [Int]
fibs = 1 : 1 : zipWith (+) fibs (tail fibs)


data Queue s a = Queue { empty :: s
                       , enqueue :: a -> s -> s
                       , dequeue :: s -> s
                       , front :: s -> a
                       }

type LQueue a = Queue [a] a
mkLQueue :: LQueue a
mkLQueue = Queue empty enqueue dequeue front where
  empty = []
  enqueue x xs = xs ++ [x]
  dequeue (_:xs) = xs
  front (x:_) = x

type FQueue a = Queue ([a] -> [a]) a
mkFQueue :: FQueue a
mkFQueue = Queue empty enqueue dequeue front where
  empty = id
  enqueue x f future = f (x:future)
  dequeue f future = tail $ f future
  front f = head $ f []


-- data IOList a = Empty | Cons a (IORef (IOList a))
-- type VQueue a = (IOList a, IORef (IOList a))
-- 
-- empty :: IO (VQueue a)
-- empty = return (Empty, error "empty queue")
-- 
-- enqueue :: a -> VQueue a -> IO (VQueue a)
-- enqueue x (Empty, _) = do e <- newIORef Empty
--                           return (Cons x e, e)
-- enqueue x (q, r) = do e <- newIORef Empty
--                       r $= Cons x e
--                       return (q, e)
-- 
-- dequeue :: VQueue a -> IO (VQueue a)
-- dequeue (Cons _ r, e) = do q <- get r
--                            case q of
--                              Empty -> empty
--                              q -> return (q, e)
-- 
-- front :: VQueue a -> a
-- front (Cons x _, _) = x
-- 
-- 
-- loop :: VQueue Int -> Int -> IO ()
-- loop q i = do print $ front q
--               q <- dequeue q
--               q <- enqueue i q
--               loop q (i+1)
-- q <- foldM (flip enqueue) q [0..1000]
-- loop q 1001

data STList s a = Empty | Cons a (STRef s (STList s a))
type SQueue s a = (STList s a, STRef s (STList s a))

s_empty :: ST s (SQueue s a)
s_empty = return (Empty, error "empty queue")

s_enqueue :: a -> SQueue s a -> ST s (SQueue s a)
s_enqueue x (Empty, _) = do e <- newSTRef Empty
                            return (Cons x e, e)
s_enqueue x (q, r) = do e <- newSTRef Empty
                        writeSTRef r $ Cons x e
                        return (q, e)

s_dequeue :: SQueue s a -> ST s (SQueue s a)
s_dequeue (Cons _ r, e) = do q <- readSTRef r
                             case q of
                               Empty -> s_empty
                               q -> return (q, e)

s_front :: SQueue s a -> a
s_front (Cons x _, _) = x

data HQueue a = HQueue (forall s. ST s (SQueue s a))

mkHQueue :: Queue (HQueue a) a
mkHQueue = Queue empty enqueue dequeue front where
  empty = HQueue s_empty
  enqueue x (HQueue get_q) = HQueue $ do q <- get_q
                                         s_enqueue x q
  dequeue (HQueue get_q) = HQueue $ do q <- get_q
                                       s_dequeue q
  front (HQueue get_q) = runST $ do q <- get_q
                                    return $ s_front q



data Tree a = Leaf a | Branch (Tree a) (Tree a) deriving (Show, Eq)
type QTree a = [(Int, Tree a)]

q_prepend :: (Int, Tree a) -> QTree a -> QTree a
q_prepend x [] = [x]
q_prepend (i, x) ((j, y):ys) | i == j = q_prepend (i+1, Branch x y) ys
q_prepend x xs = x:xs

q_right :: Tree a -> a
q_right (Leaf x) = x
q_right (Branch _ x) = q_right x

q_consume_right :: (Int, Tree a) -> QTree a
q_consume_right (1, Leaf _) = []
q_consume_right (n, Branch x y) = [(n-1, x)] ++ q_consume_right (n-1, y)

mkTQueue :: Queue (QTree a) a
mkTQueue = Queue empty enqueue dequeue front where
  empty = []
  enqueue x = q_prepend (1, Leaf x)
  dequeue xs = take (length xs - 1) xs ++ q_consume_right (last xs)
  front xs = q_right $ snd $ last xs



print_dequeue :: Show a => Queue s a -> s -> IO s
print_dequeue q s = do print $ front q s
                       return $ dequeue q s

test_queue :: Queue s Char -> IO ()
test_queue q = do s <- return $ empty q
                  s <- return $ enqueue q 'a' s
                  s <- return $ enqueue q 'b' s
                  s <- return $ enqueue q 'c' s
                  s <- print_dequeue q s
                  s <- return $ enqueue q 'd' s
                  s <- print_dequeue q s
                  s <- print_dequeue q s
                  s <- print_dequeue q s
                  s <- return $ enqueue q 'e' s
                  s <- print_dequeue q s
                  return ()

enqueue_dequeue :: Show a => Queue s a -> s -> a -> IO s
enqueue_dequeue q s i = do s <- print_dequeue q s
                           return $ enqueue q i s

stress_test :: Queue s Int -> IO ()
stress_test q = do s <- return $ empty q
                   s <- return $ foldr (enqueue q) s $ reverse [0..1000]
                   s <- foldM (enqueue_dequeue q) s [1001..10000]
                   return ()

main = do putStrLn "typechecks."
          -- test_queue mkLQueue
          -- test_queue mkFQueue
          -- test_queue mkHQueue
          -- test_queue mkTQueue
          stress_test mkTQueue
