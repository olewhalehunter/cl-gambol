#|
  This file is a part of gambol project.
  Copyright (c) 2013 Stephen A. Goss (steveth45@gmail.com)
|#

(in-package :cl-user)
(defpackage gambol-test-asd
  (:use :cl :asdf))
(in-package :gambol-test-asd)

(defsystem gambol-test
  :author "Stephen A. Goss"
  :license "MIT"
  :depends-on (:gambol
               :cl-test-more)
  :components ((:module "t"
                :components
                ((:file "gambol"))))
  :perform (load-op :after (op c) (asdf:clear-system c)))
