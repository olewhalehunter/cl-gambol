
(ql:quickload "gambol")
(ql:quickload "lift")

(defpackage :gambol-speed
  (:use :cl :gambol))

(in-package :gambol-speed)

(defmacro report-lips (&rest body)
  (let ((start-time (gensym))
        (body-value (gensym))
        (end-time (gensym)))
    `(let ((,start-time (get-internal-real-time))
           (*lips* 0))
       (let ((,body-value (progn ,@body)))
         (let ((,end-time (get-internal-real-time)))
           (let ((lips (/ *lips* (/ (float (- ,end-time ,start-time))
                                    internal-time-units-per-second))))
             (format t "LIPS: ~A~%" lips)))
         ,body-value))))

(defun do-speed-test ()
  (report-lips
   (*- (factorial 0 1))
   (*- (factorial ?n ?f)
       (lop (> ?n 0))
       (is ?n1 (lop (1- ?n)))
       (factorial ?n1 ?f1)
       (is ?f (lop (* ?n ?f1))))
   (dotimes (x 5000)
     (pl-solve-all '((factorial 33 ?f))))))

(format t "running tests~%")
(do-speed-test)
