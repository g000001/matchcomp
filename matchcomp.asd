;;;; matchcomp.asd -*- Mode: Lisp;-*- 

(cl:in-package :asdf)

(defsystem :matchcomp
  :serial t
  :depends-on (:fiveam
               :named-readtables
               :rnrs-compat
               :srfi-23
               :srfi-45)
  :components ((:file "package")
               (:file "matchcomp")))

(defmethod perform ((o test-op) (c (eql (find-system :matchcomp))))
  (load-system :matchcomp)
  (or (flet ((_ (pkg sym)
               (intern (symbol-name sym) (find-package pkg))))
         (let ((result (funcall (_ :fiveam :run) (_ :matchcomp.internal :matchcomp))))
           (funcall (_ :fiveam :explain!) result)
           (funcall (_ :fiveam :results-status) result)))
      (error "test-op failed") ))

