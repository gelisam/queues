{-# LANGUAGE GADTs, DeriveFunctor, Rank2Types #-}

import Data.IORef
import Data.STRef
import Data.StateVar
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans


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

data AntiList a z = AntiCons (a -> AntiList a z) | AntiNil z

feed_into :: [a] -> AntiList a z -> z
feed_into _ (AntiNil z) = z
feed_into (x:xs) (AntiCons f) = feed_into xs $ f x


data EnqueueList a z = Enqueue a (EnqueueList a z) | Return z

unEnqueueList :: EnqueueList a z -> ([a], z)
unEnqueueList (Return z) = ([], z)
unEnqueueList (Enqueue x es) = let (xs, z) = unEnqueueList es
                                in (x:xs, z)

type CCQueue a z = [a] -> EnqueueList a z

cc_queue :: CCQueue a z -> z
cc_queue f = z where
  (xs, z) = unEnqueueList $ f xs

cc_enqueue :: a -> CCQueue a z -> CCQueue a z
cc_enqueue x cc xs = Enqueue x $ cc xs

cc_dequeue :: (a -> CCQueue a z) -> CCQueue a z
cc_dequeue cc (x:xs) = cc x xs


cc_print_dequeue :: Show a => (IO () -> CCQueue a z) -> CCQueue a z
cc_print_dequeue cc = cc_dequeue $ \x ->
                        cc $ print x

cc_test_queue :: IO ()
cc_test_queue = cc_queue $
                cc_enqueue 'a' $
                cc_enqueue 'b' $
                cc_enqueue 'c' $
                cc_print_dequeue $ \io1 ->
                cc_enqueue 'd' $
                cc_print_dequeue $ \io2 ->
                cc_print_dequeue $ \io3 ->
                cc_print_dequeue $ \io4 ->
                cc_enqueue 'e' $
                cc_print_dequeue $ \io5 ->
                (\_ -> Return $ do io1
                                   io2
                                   io3
                                   io4
                                   io5
                                   return ())


data RQueue a z = RQueue { unRQueue :: [a] -> ([a], z) }

instance Monad (RQueue a) where
  return x = RQueue $ \_ -> ([], x)
  q >>= f = RQueue $ \xs -> let (ys, a) = unRQueue q xs
                                (ys', b) = unRQueue (f a) xs
                             in (ys ++ ys', b)

runRQueue :: RQueue [a] z -> z
runRQueue q = z where
  (xs, z) = unRQueue q xs

data RQueueT a m z = RQueueT { runRQueueT :: [a] -> m ([a], z) }

instance Monad m => Monad (RQueueT a m) where
  return x = RQueueT $ \_ -> return ([], x)
  x >>= f = RQueueT $ \xs -> do (ys, a) <- runRQueueT x xs
                                (ys', b) <- runRQueueT (f a) xs
                                return (ys ++ ys', b)

instance MonadTrans (RQueueT a) where
  lift mx = RQueueT $ \_ -> do x <- mx
                               return ([], x)



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
          --test_queue mkFQueue
          --test_queue mkHQueue
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
