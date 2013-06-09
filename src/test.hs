import Data.IORef
import Data.STRef
import Data.StateVar
import Control.Monad
import Control.Monad.ST


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


data IOQueue s a = IOQueue { io_empty :: IO s
                           , io_enqueue :: a -> s -> IO s
                           , io_dequeue :: s -> IO s
                           , io_front :: s -> a
                           }

data IOList a = IOEmpty | IOCons a (IORef (IOList a))
type VQueue a = (IOList a, IORef (IOList a))

do_empty :: IO (VQueue a)
do_empty = return (IOEmpty, error "empty queue")

do_enqueue :: a -> VQueue a -> IO (VQueue a)
do_enqueue x (IOEmpty, _) = do e <- newIORef IOEmpty
                               return (IOCons x e, e)
do_enqueue x (q, r) = do e <- newIORef IOEmpty
                         r $= IOCons x e
                         return (q, e)
   
do_dequeue :: VQueue a -> IO (VQueue a)
do_dequeue (IOCons _ r, e) = do q <- get r
                                case q of
                                  IOEmpty -> do_empty
                                  q -> return (q, e)
   
do_front :: VQueue a -> a
do_front (IOCons x _, _) = x


mkVQueue :: IOQueue (VQueue a) a
mkVQueue = IOQueue do_empty do_enqueue do_dequeue do_front


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

(...) = (.) . (.)

mkSTQueue :: IOQueue (SQueue RealWorld a) a
mkSTQueue = IOQueue (stToIO s_empty)
                    (stToIO ... s_enqueue)
                    (stToIO . s_dequeue)
                    s_front


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
                   s <- return $ foldr (enqueue q) s $ reverse [0..10000]
                   s <- foldM (enqueue_dequeue q) s [1001..31001]
                   return ()


io_print_dequeue :: Show a => IOQueue s a -> s -> IO s
io_print_dequeue q s = do print $ io_front q s
                          io_dequeue q s

io_enqueue_dequeue :: Show a => IOQueue s a -> s -> a -> IO s
io_enqueue_dequeue q s i = do s <- io_print_dequeue q s
                              io_enqueue q i s
   
io_stress_test :: IOQueue s Int -> IO ()
io_stress_test q = do s <- io_empty q
                      s <- foldM (flip $ io_enqueue q) s $ [0..10000]
                      s <- foldM (io_enqueue_dequeue q) s [1001..31001]
                      return ()

io_queue :: Queue s a -> IOQueue s a
io_queue (Queue empty enqueue dequeue front) = IOQueue (return empty)
                                                       (return ... enqueue)
                                                       (return . dequeue)
                                                       front


main = do putStrLn "typechecks."
          
          -- make sure the queues behave as queues.
          -- this is not an automated test; the output should be:
          --   'a'
          --   'b'
          --   'c'
          --   'd'
          --   'e'
          --test_queue mkLQueue
          --test_queue mkTQueue
          --cc_test_queue
          
          --     \   buffer size              
          -- #ops \ 100     1k   10k
          --  10k  0.02s 0.15s  5.7s
          --  20k  0.04s 0.30s 12.0s
          --  30k  0.06s 0.45s 19.1s
          -- * increasing the buffer decreases the performance
          --stress_test mkLQueue
           
          --     \   buffer size              
          -- #ops \ 100     1k   10k
          --  10k  0.02s 0.02s 0.02s
          --  20k  0.03s 0.04s 0.04s
          --  30k  0.05s 0.05s 0.06s
          -- * buffer size has no impact on performance
          --stress_test mkTQueue
          
          -- We now switch to a different implementation of stress_test,
          -- which runs inside IO. The previous and the next test apply
          -- the two stress_test implementations to the same queue
          -- implementation, to make sure the results are comparable.
          
          --     \   buffer size              
          -- #ops \ 100     1k   10k
          --  10k  0.02s 0.02s 0.03s
          --  20k  0.04s 0.04s 0.05s
          --  30k  0.05s 0.05s 0.07s
          -- * similar to the non-IO results, accuracy ~0.01
          --io_stress_test $ io_queue mkTQueue
          
          --     \   buffer size              
          -- #ops \ 100     1k   10k
          --  10k  0.01s 0.02s 0.02s
          --  20k  0.02s 0.03s 0.03s
          --  30k  0.04s 0.04s 0.04s
          -- * buffer size has no impact on performance
          --io_stress_test mkVQueue
          
          --     \   buffer size              
          -- #ops \ 100     1k   10k
          --  10k  0.02s 0.02s 0.02s
          --  20k  0.03s 0.03s 0.04s
          --  30k  0.04s 0.04s 0.05s
          -- * buffer size has no impact on performance
          --io_stress_test mkSTQueue
