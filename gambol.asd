(in-package :cl-user)
(defpackage gambol-asd
  (:use :cl :asdf))
(in-package :gambol-asd)

(defsystem gambol
  :version "0.05"
  :author "Stephen A. Goss"
  :license "MIT"
  :depends-on ()
  :components ((:module "src"
                :components
                ((:file "gambol"))))
  :description "A buggy, incomplete implementation of Prolog."
  :long-description
  #.(with-open-file (stream (merge-pathnames
                             #p"README.markdown"
                             (or *load-pathname* *compile-file-pathname*))
                            :if-does-not-exist nil
                            :direction :input)
      (when stream
        (let ((seq (make-array (file-length stream)
                               :element-type 'character
                               :fill-pointer t)))
          (setf (fill-pointer seq) (read-sequence seq stream))
          seq)))
  :in-order-to ((test-op (load-op gambol-test))))
