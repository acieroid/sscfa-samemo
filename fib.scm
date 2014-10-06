(letrec ((fib (lambda (n)
                (if (<= n 2)
                  n
                  (let ((fibn1 (fib (- n 1))))
                    (let ((fibn2 (fib (- n 2))))
                      (+ fibn1 fibn2)))))))
  (fib 4))
