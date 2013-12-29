;;;; package.lisp

(cl:in-package :cl-user)

(defpackage :matchcomp
  (:use)
  (:export :match-lambda
           :match-all-lambda
           :match-case))

(defpackage :matchcomp.internal
  (:use :matchcomp :rnrs :named-readtables :fiveam :srfi-23)
  (:shadowing-import-from :srfi-45 :delay :force)
  (:shadowing-import-from :cl :gensym))

