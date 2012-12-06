;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: variables.lisp
;;; The contents of this file are subject to the Mozilla Public License
;;; Version 1.1 (the "License"); you may not use this file except in
;;; compliance with the License. You may obtain a copy of the License at
;;; http://www.mozilla.org/MPL/
;;;
;;; Software distributed under the License is distributed on an "AS IS"
;;; basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
;;; License for the specific language governing rights and limitations
;;; under the License.
;;;
;;; The Original Code is SNARK.
;;; The Initial Developer of the Original Code is SRI International.
;;; Portions created by the Initial Developer are Copyright (C) 1981-2011.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

(defconstant $number-of-variable-blocks 1000)
(defconstant $number-of-variables-per-block 6000)
(defconstant $number-of-variables-in-blocks (* $number-of-variable-blocks $number-of-variables-per-block))

(defvar *variables*)				;table to translate (number sort) pairs to variables
(defvar *next-variable-number* 0)		;next number to use for new unique variable
(declaim (type integer *next-variable-number*))

(defstruct (variable
            (:constructor make-variable0 (number sort))
            (:copier nil)
            (:print-function print-term3))
  number
  sort)

(defun initialize-variables ()
  (setf *variables* (make-sparse-matrix :rows t))
  (setf *next-variable-number* $number-of-variables-in-blocks)
  nil)

(defun make-variable (&optional sort number)
  ;; if number is specified, return canonical variable for that sort and number
  ;; if number is not specified, create a new unique variable with that sort
  ;; variable identity must be testable by EQ
  ;; this variable representation must also be understood by dereference
  ;;
  ;; don't create last variable in a block; when incrementing variable numbers,
  ;; the following variable would be in the next block creating confusion
  (cond
   (number
    (let* ((s (and (not (top-sort? sort)) sort))
           (s# (funcall *standard-equal-numbering* :lookup s)))
      (or (sparef *variables* number s#)
          (progn
            (cl:assert (<= 0 number))
            (cl:assert (< number $number-of-variables-in-blocks))
            (cl:assert (/= 0 (mod (+ number 1) $number-of-variables-per-block)))
            (setf (sparef *variables* number s#) (make-variable0 number (or sort (top-sort))))))))
   (t
    (setf *next-variable-number* (+ (setf number *next-variable-number*) 1))
    (make-variable0 number (or sort (top-sort))))))

(defun declare-variable (name &key (sort (top-sort-name) sort-supplied-p))
  ;; return same variable every time for same input free variable
  (can-be-variable-name name 'error)
  (when (not (top-sort-name? sort))
    (setf sort (the-sort sort))
    (cl:assert (not (unsortable-variable-name name))
               ()
               "Cannot declare ~A as variable of sort ~A; ~A is unsorted."
               name (sort-name sort) name))
  (let ((v (input-variable name)))
    (cond
     ((eq none (variable-sort v))		;new variable
      (unless sort-supplied-p
        (setf sort (if (use-variable-name-sorts?) (sort-from-variable-name name) (top-sort))))
      (setf (variable-sort v) sort))
     (sort-supplied-p
      (cl:assert (same-sort? sort (variable-sort v)) ()
                 "Cannot declare ~A as variable of sort ~A; ~A is of sort ~A."
                 name (sort-name sort) name (sort-name (variable-sort v)))))
    v))

(defun unsortable-variable-name (name)
  ;; SNARK output uses ?, ?X, ?Y, ?Z, ?U, ?V, ?W, ?X1, ?Y1, ?Z1, ?U1, ?V1, ?W1, ...
  ;; as unsorted variables; to enable SNARK to faithfully input its own output,
  ;; don't allow these variables to be declared with a sort
  (let* ((s (symbol-name name))
         (v (variable-symbol-prefixed-p s (list (first (variable-symbol-prefixes?))))))
    (and v
         (let ((len (length s)))
           (or (eql len v)
               (and (member (char s v) '(#\X #\Y #\Z #\U #\V #\W #\x #\y #\z #\u #\v #\w))
                    (or (eql (+ 1 v) len)
                        (null (position-if-not #'digit-char-p s :start (+ 1 v))))))))))

(defun sort-from-variable-name (name)
  ;; try to interpret as a sort the substring between ?* at start and [#]digit* at end
  (let* ((sort (top-sort))
         (s (symbol-name name))
         (m (or (variable-symbol-prefixed-p s) 0))
         (n (position-if-not #'digit-char-p s :from-end t)))
    (unless (eql #\# (char s n))
      (setf n (+ n 1)))
    (when (<= 2 (- n m))
      (mvlet (((:values sym found) (find-symbol (subseq s m n) :snark-user)))
        (when found
          (let ((v (find-symbol-table-entry sym :sort)))
            (when (neq none v)
              (setf sort v))))))
    sort))

(defun variable-block (n)
  (declare (fixnum n))
  (cl:assert (< 0 n $number-of-variable-blocks))
  (* $number-of-variables-per-block n))

(defun variable-block-0-p (varnum)
  (declare (fixnum varnum))
  (> $number-of-variables-per-block varnum))

;;; variables.lisp EOF
