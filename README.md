queues
======

Compare the performance of a few Haskell queue implementations.


results
-------

If your queue has 100 items or less in it, then it doesn't matter.

Otherwise, use [Data.Sequence](http://hackage.haskell.org/package/containers), it has the same or slightly better performance as everything else I have tried, and its API is much simpler than those.
