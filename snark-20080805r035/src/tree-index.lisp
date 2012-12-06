;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: tree-index.lisp
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
;;; Portions created by the Initial Developer are Copyright (C) 1981-2008.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

(defvar *tree-index*)

(defstruct (tree-index
	     (:constructor make-tree-index0 (entry-constructor))
	     (:copier nil))
  (entry-constructor nil :read-only t)		;term->entry function for new entry insertion
  (node-counter (make-counter 1) :read-only t)
  (entry-counter (make-counter) :read-only t)
  (top-node (make-tree-index-internal-node) :read-only t)
  (retrieve-generalization-calls 0 :type integer)	;number of generalization retrieval calls
  (retrieve-generalization-count 0 :type integer)
  (retrieve-instance-calls 0 :type integer)		;    "     instance          "
  (retrieve-instance-count 0 :type integer)
  (retrieve-unifiable-calls 0 :type integer)		;    "     unifiable         "
  (retrieve-unifiable-count 0 :type integer)
  (retrieve-variant-calls 0 :type integer)		;    "     variant           "
  (retrieve-variant-count 0 :type integer)
  (retrieve-all-calls 0 :type integer)			;    "     all               "
  (retrieve-all-count 0 :type integer))

(defstruct (tree-index-internal-node
            (:copier nil))
  (variable-child-node nil)			;nil or node
  (constant-indexed-child-nodes nil)		;constant# -> node sparse-vector
  (function-indexed-child-nodes nil))		;function# -> node sparse-vector

(defstruct (tree-index-leaf-node
            (:include sparse-vector (snark-sparse-array::default-value none :read-only t))
            (:copier nil))
  )

(defmacro tree-index-leaf-node-entries (n)
  n)

(defstruct (index-entry
	     (:constructor make-index-entry (term))
	     (:copier nil))
  (term nil :read-only t))

(defun make-tree-index (&key (entry-constructor #'make-index-entry))
  (setf *tree-index* (make-tree-index0 entry-constructor)))

(definline tree-index-internal-node-variable-indexed-child-node (node &optional create internal)
  (or (tree-index-internal-node-variable-child-node node)
      (and create
           (progn
             (increment-counter (tree-index-node-counter *tree-index*))
             (setf (tree-index-internal-node-variable-child-node node)
                   (if internal
                       (make-tree-index-internal-node)
                       (make-tree-index-leaf-node)))))))

(definline tree-index-internal-node-constant-indexed-child-node (const node &optional create internal)
  (let ((children (tree-index-internal-node-constant-indexed-child-nodes node)))
    (unless children
      (when create
        (setf children (setf (tree-index-internal-node-constant-indexed-child-nodes node) (make-sparse-vector)))))
    (and children
         (let ((const# (constant-number const)))
           (or (sparef children const#)
               (and create
                    (progn
                      (increment-counter (tree-index-node-counter *tree-index*))
                      (setf (sparef children const#)
                            (if internal
                                (make-tree-index-internal-node)
                                (make-tree-index-leaf-node))))))))))

(definline tree-index-internal-node-function-indexed-child-node (fn node &optional create internal)
  (let ((children (tree-index-internal-node-function-indexed-child-nodes node)))
    (unless children
      (when create
        (setf children (setf (tree-index-internal-node-function-indexed-child-nodes node) (make-sparse-vector)))))
    (and children
         (let ((fn# (function-number fn)))
           (or (sparef children fn#)
               (and create
                    (progn
                      (increment-counter (tree-index-node-counter *tree-index*))
                      (setf (sparef children fn#)
                            (if internal
                                (make-tree-index-internal-node)
                                (make-tree-index-leaf-node))))))))))

(definline function-tree-index-lookup-args (fn term)
  ;; fn = (head term) unless term is nil (not specified)
  (ecase (function-index-type fn)
    ((nil)
     (cond
      ((function-unify-code fn)
       nil)
      (t
       (let ((arity (function-arity fn)))
         (if (eq :any arity) (list (args term)) (args term))))))
    (:commute
     ;; index all arguments, lookup with first two in order and commuted
     ;; (a b c d) -> 4, (c d a b), (c d (%index-or (a b) (b a))) for arity 4
     ;; (a b c d) -> 3, ((c d) a b), ((c d) (%index-or (a b) (b a))) for arity :any
     (let ((arity (function-arity fn)))
       (let* ((args (args term))
              (l (rest (rest args)))
              (a (first args))
              (b (second args))
              (v (list (list '%index-or (if l (list a b) args) (list b a)))))
         (cond
          ((eq :any arity)
           (cons l v))
          (l
           (append l v))
          (t
           v)))))
    (:bag-cons
     ;; index only second argument
     (list (second (args term))))
    (:jepd
     ;; index only first two arguments, lookup with first two in order and commuted
     ;; (a b c) -> 2, (a b), ((%index-or (a b) (b a)))
     (let* ((args (args term))
            (a (first args))
            (b (second args)))
       (list (list '%index-or (list a b) (list b a)))))
    (:hash-but-dont-index
     nil)))

(definline function-tree-index-args (fn term)
  (ecase (function-index-type fn)
    ((nil)
     (cond
      ((function-unify-code fn)
       nil)
      (t
       (let ((arity (function-arity fn)))
         (if (eq :any arity) (list (args term)) (args term))))))
    (:commute
     (let ((arity (function-arity fn)))
       (let* ((args (args term))
              (l (rest (rest args)))
              (v (if l (list (first args) (second args)) args)))
         (cond
          ((eq :any arity)
           (cons l v))
          (l
           (append l v))
          (t
           v)))))
    (:bag-cons
     (list (second (args term))))
    (:jepd
     (let ((args (args term)))
       (list (first args) (second args))))
    (:hash-but-dont-index
     nil)))

(definline function-tree-index-arity (fn)
  (ecase (function-index-type fn)
    ((nil)
     (cond
      ((function-unify-code fn)
       0)
      (t
       (let ((arity (function-arity fn)))
         (if (eq :any arity) 1 arity)))))
    (:commute
     (let ((arity (function-arity fn)))
       (if (eq :any arity) 3 arity)))
    (:bag-cons
     1)
    (:jepd
     2)
    (:hash-but-dont-index
     0)))

(defun simply-indexed-p (term &optional subst)
  (dereference
   term subst
   :if-variable t
   :if-constant t
   :if-compound-cons (and (simply-indexed-p (carc term))
                          (simply-indexed-p (cdrc term)))
   :if-compound-appl (and (let ((fn (heada term)))
                            (ecase (function-index-type fn)
                              ((nil)
                               (null (function-unify-code fn)))
                              (:commute
                               nil)
                              (:bag-cons
                               t)
                              (:hash-but-dont-index
                               t)
                              (:jepd
                               nil)))
                          (dolist (arg (argsa term) t)
                            (unless (simply-indexed-p arg subst)
                              (return nil))))))

(definline tree-index-build-path-for-terms (terms node internal)
  (if internal
      (dolist (x terms node)
        (setf node (tree-index-build-path-for-term x node t)))
      (dotails (l terms node)
        (setf node (tree-index-build-path-for-term (first l) node (rest l))))))

(defun tree-index-build-path-for-term (term node &optional internal)
  (dereference
   term nil
   :if-variable (tree-index-internal-node-variable-indexed-child-node node t internal)
   :if-constant (tree-index-internal-node-constant-indexed-child-node term node t internal)
   :if-compound (let* ((head (head term))
                       (args (function-tree-index-args head term)))
                  (if (null args)
                      (tree-index-internal-node-function-indexed-child-node head node t internal)
                      (tree-index-build-path-for-terms args (tree-index-internal-node-function-indexed-child-node head node t t) internal)))))

(definline tree-index-path-for-terms (terms path)
  (dolist (x terms path)
    (when (null (setf path (tree-index-path-for-term x path)))
      (return nil))))

(defun tree-index-path-for-term (term path)
  (let ((node (first path)))
    (dereference
     term nil
     :if-variable (let ((n (tree-index-internal-node-variable-indexed-child-node node)))
		    (and n (list* n 'variable path)))
     :if-constant (let ((n (tree-index-internal-node-constant-indexed-child-node term node)))
		    (and n (list* n 'constant term path)))
     :if-compound (let* ((head (head term))
			 (n (tree-index-internal-node-function-indexed-child-node head node)))
		    (and n (let ((args (function-tree-index-args head term)))
			     (if (null args)
				 (list* n 'function head path)
				 (tree-index-path-for-terms args (list* n 'function head path)))))))))

(defun tree-index-insert (term &optional entry)
  (let* ((tree-index *tree-index*)
         (entries (tree-index-leaf-node-entries (tree-index-build-path-for-term term (tree-index-top-node tree-index)))))
    (cond
     ((null entry)
      (prog->
        (map-sparse-vector entries :reverse t ->* e)
        (when (or (eql term (index-entry-term e)) (and (test-option38?) (equal-p term (index-entry-term e))))
          (return-from tree-index-insert e)))
      (setf entry (funcall (tree-index-entry-constructor tree-index) term)))
     (t
      (cl:assert (eql term (index-entry-term entry)))
      (prog->
        (map-sparse-vector entries :reverse t ->* e)
        (when (eq entry e)
          (return-from tree-index-insert e))
        (when (or (eql term (index-entry-term e)) (and (test-option38?) (equal-p term (index-entry-term e))))
          (error "There is already a tree-index entry for term ~A." term)))))
    (increment-counter (tree-index-entry-counter tree-index))
    (setf (sparef entries (nonce)) entry)))

(defun tree-index-delete (term &optional entry)
  (let* ((tree-index *tree-index*)
	 (path (tree-index-path-for-term term (list (tree-index-top-node tree-index)))))
    (when path
      (let* ((entries (tree-index-leaf-node-entries (pop path)))
	     (k (cond
		  ((null entry)
		   (prog->
		     (map-sparse-vector-with-indexes entries :reverse t ->* e k)
		     (when (eql term (index-entry-term e))
		       (return-from prog-> k))))
		  (t
		   (cl:assert (eql term (index-entry-term entry)))
		   (prog->
		     (map-sparse-vector-with-indexes entries :reverse t ->* e k)
		     (when (eq entry e)
		       (return-from prog-> k)))))))
	(when k
	  (decrement-counter (tree-index-entry-counter tree-index))
	  (setf (sparef entries k) none)
	  (when (eql 0 (sparse-vector-count entries))
            (let ((node-counter (tree-index-node-counter tree-index))
                  parent)
	      (loop
	        (ecase (pop path)
		  (function
                   (let ((k (function-number (pop path))))
		     (setf (sparef (tree-index-internal-node-function-indexed-child-nodes (setf parent (pop path))) k) nil)))
		  (constant
                   (let ((k (constant-number (pop path))))
		     (setf (sparef (tree-index-internal-node-constant-indexed-child-nodes (setf parent (pop path))) k) nil)))
		  (variable
		   (setf (tree-index-internal-node-variable-child-node (setf parent (pop path))) nil)))
	        (decrement-counter node-counter)
	        (unless (and (rest path)		;not top node
                             (null (tree-index-internal-node-variable-child-node parent))
			     (eql 0 (sparse-vector-count (tree-index-internal-node-function-indexed-child-nodes parent)))
			     (eql 0 (sparse-vector-count (tree-index-internal-node-constant-indexed-child-nodes parent))))
		  (return)))))
	  t)))))

(defmacro map-tree-index-entries (&key if-variable if-constant if-compound count-call count-entry)
  (declare (ignorable count-call count-entry))
  `(labels
     ((map-for-term (cc term node)
        (dereference
         term subst
         :if-variable ,if-variable
         :if-constant ,if-constant
         :if-compound ,if-compound))
      (map-for-terms (cc terms node)
        (cond
         ((null terms)
          (funcall cc node))
         (t
          (let ((term (pop terms)))
            (cond
             ((and (consp term) (eq '%index-or (first term)))
              (cond
               ((null terms)
                (prog->
                  (dolist (rest term) ->* terms1)
                  (map-for-terms terms1 node ->* node)
                  (funcall cc node)))
               (t
                (prog->
                  (dolist (rest term) ->* terms1)
                  (map-for-terms terms1 node ->* node)
                  (map-for-terms terms node ->* node)
                  (funcall cc node)))))
             (t
              (cond
               ((null terms)
                (prog->
                  (map-for-term term node ->* node)
                  (funcall cc node)))
               (t
                (prog->
                  (map-for-term term node ->* node)
                  (map-for-terms terms node ->* node)
                  (funcall cc node))))))))))
      (skip-terms (cc n node)
        (declare (type fixnum n))
        (cond
         ((= 1 n)
          (progn
            (prog->
              (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
              (funcall cc node))
            (prog->
              (tree-index-internal-node-constant-indexed-child-nodes node ->nonnil constant-indexed-children)
              (map-sparse-vector constant-indexed-children ->* node)
              (funcall cc node))
            (prog->
              (tree-index-internal-node-function-indexed-child-nodes node ->nonnil function-indexed-children)
              (map-sparse-vector-with-indexes function-indexed-children ->* node fn#)
              (skip-terms (function-tree-index-arity (symbol-numbered fn#)) node ->* node)
              (funcall cc node))))
         ((= 0 n)
          (funcall cc node))
         (t
          (progn
            (decf n)
            (prog->
              (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
              (skip-terms n node ->* node)
              (funcall cc node))
            (prog->
              (tree-index-internal-node-constant-indexed-child-nodes node ->nonnil constant-indexed-children)
              (map-sparse-vector constant-indexed-children ->* node)
              (skip-terms n node ->* node)
              (funcall cc node))
            (prog->
              (tree-index-internal-node-function-indexed-child-nodes node ->nonnil function-indexed-children)
              (map-sparse-vector-with-indexes function-indexed-children ->* node fn#)
              (skip-terms (+ n (function-tree-index-arity (symbol-numbered fn#))) node ->* node)
              (funcall cc node)))))))
     (let ((tree-index *tree-index*))
;;     ,count-call
       (cond
        ((simply-indexed-p term subst)
         (prog->
           (map-for-term term (tree-index-top-node tree-index) ->* leaf-node)
           (map-sparse-vector (tree-index-leaf-node-entries leaf-node) :reverse t ->* e)
;;         ,count-entry
           (funcall cc e)))
        (t
         (prog->
           (quote nil -> seen)
           (map-for-term term (tree-index-top-node tree-index) ->* leaf-node)
           (when (do ((s seen (cdrc s)))	;(not (member leaf-node seen))
                     ((null s)
                      t)
                   (when (eq leaf-node (carc s))
                     (return nil)))
             (prog->
               (map-sparse-vector (tree-index-leaf-node-entries leaf-node) :reverse t ->* e)
;;             ,count-entry
               (funcall cc e))
             (setf seen (cons leaf-node seen)))))))
     nil))

(defun map-tree-index-instance-entries (cc term subst)
  (map-tree-index-entries
   :count-call (incf (tree-index-retrieve-instance-calls tree-index))
   :count-entry (incf (tree-index-retrieve-instance-count tree-index))
   :if-variable (prog->
                  (skip-terms 1 node ->* node)
                  (funcall cc node))
   :if-constant (prog->
                  (tree-index-internal-node-constant-indexed-child-node term node ->nonnil node)
                  (funcall cc node))
   :if-compound (prog->
                  (head term -> head)
                  (tree-index-internal-node-function-indexed-child-node head node ->nonnil node)
                  (map-for-terms (function-tree-index-lookup-args head term) node ->* node)
                  (funcall cc node))))

(defun map-tree-index-generalization-entries (cc term subst)
  ;; in snark-20060805 vs. snark-20060806 test over TPTP,
  ;; constant and compound lookup before variable lookup outperforms
  ;; variable lookup before constant and compound lookup
  (map-tree-index-entries
   :count-call (incf (tree-index-retrieve-generalization-calls tree-index))
   :count-entry (incf (tree-index-retrieve-generalization-count tree-index))
   :if-variable (prog->
                  (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
                  (funcall cc node))
   :if-constant (progn
                  (prog->
                    (tree-index-internal-node-constant-indexed-child-node term node ->nonnil node)
                    (funcall cc node))
                  (prog->
                    (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
                    (funcall cc node)))
   :if-compound (progn
                  (prog->
                    (head term -> head)
                    (tree-index-internal-node-function-indexed-child-node head node ->nonnil node)
                    (map-for-terms (function-tree-index-lookup-args head term) node ->* node)
                    (funcall cc node))
                  (prog->
                    (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
                    (funcall cc node)))))

(defun map-tree-index-unifiable-entries (cc term subst)
  (map-tree-index-entries
   :count-call (incf (tree-index-retrieve-unifiable-calls tree-index))
   :count-entry (incf (tree-index-retrieve-unifiable-count tree-index))
   :if-variable (prog->
                  (skip-terms 1 node ->* node)
                  (funcall cc node))
   :if-constant (progn
                  (prog->
                    (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
                    (funcall cc node))
                  (prog->
                    (tree-index-internal-node-constant-indexed-child-node term node ->nonnil node)
                    (funcall cc node)))
   :if-compound (progn
                  (prog->
                    (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
                    (funcall cc node))
                  (prog->
                    (head term -> head)
                    (tree-index-internal-node-function-indexed-child-node head node ->nonnil node)
                    (map-for-terms (function-tree-index-lookup-args head term) node ->* node)
                    (funcall cc node)))))

(defun map-tree-index-variant-entries (cc term subst)
  (map-tree-index-entries
   :count-call (incf (tree-index-retrieve-variant-calls tree-index))
   :count-entry (incf (tree-index-retrieve-variant-count tree-index))
   :if-variable (prog->
                  (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
                  (funcall cc node))
   :if-constant (prog->
                  (tree-index-internal-node-constant-indexed-child-node term node ->nonnil node)
                  (funcall cc node))
   :if-compound (prog->
                  (head term -> head)
                  (tree-index-internal-node-function-indexed-child-node head node ->nonnil node)
                  (map-for-terms (function-tree-index-lookup-args head term) node ->* node)
                  (funcall cc node))))

(defun map-tree-index-all-entries (cc)
  (let ((term (make-variable nil 0))
        (subst nil))
    (map-tree-index-entries
     :count-call (incf (tree-index-retrieve-all-calls tree-index))
     :count-entry (incf (tree-index-retrieve-all-count tree-index))
     :if-variable (prog->
                    (skip-terms 1 node ->* node)
                    (funcall cc node)))))

(definline map-tree-index (cc type term &optional subst)
  (ecase type
    (:generalization
     (map-tree-index-generalization-entries cc term subst))
    (:instance
     (map-tree-index-instance-entries cc term subst))
    (:unifiable
     (map-tree-index-unifiable-entries cc term subst))
    (:variant
     (map-tree-index-variant-entries cc term subst))))

(defun print-tree-index (&key terms nodes)
  (let ((index *tree-index*))
    (mvlet (((:values current peak added deleted) (counter-values (tree-index-entry-counter index))))
      (format t "~%; Tree-index has ~:D entr~:@P (~:D at peak, ~:D added, ~:D deleted)." current peak added deleted))
    (mvlet (((:values current peak added deleted) (counter-values (tree-index-node-counter index))))
      (format t "~%; Tree-index has ~:D node~:P (~:D at peak, ~:D added, ~:D deleted)." current peak added deleted))
    (unless (eql 0 (tree-index-retrieve-variant-calls index))
      (format t "~%; Tree-index retrieved ~:D variant term~:P in ~:D call~:P."
              (tree-index-retrieve-variant-count index)
              (tree-index-retrieve-variant-calls index)))
    (unless (eql 0 (tree-index-retrieve-generalization-calls index))
      (format t "~%; Tree-index retrieved ~:D generalization term~:P in ~:D call~:P."
              (tree-index-retrieve-generalization-count index)
              (tree-index-retrieve-generalization-calls index)))
    (unless (eql 0 (tree-index-retrieve-instance-calls index))
      (format t "~%; Tree-index retrieved ~:D instance term~:P in ~:D call~:P."
              (tree-index-retrieve-instance-count index)
              (tree-index-retrieve-instance-calls index)))
    (unless (eql 0 (tree-index-retrieve-unifiable-calls index))
      (format t "~%; Tree-index retrieved ~:D unifiable term~:P in ~:D call~:P."
              (tree-index-retrieve-unifiable-count index)
              (tree-index-retrieve-unifiable-calls index)))
    (unless (eql 0 (tree-index-retrieve-all-calls index))
      (format t "~%; Tree-index retrieved ~:D unrestricted term~:P in ~:D call~:P."
              (tree-index-retrieve-all-count index)
              (tree-index-retrieve-all-calls index)))
    (when (or nodes terms)
      (print-index* (tree-index-top-node index) nil terms))))

(defun print-index* (node revpath print-terms)
  (prog->
    (map-index-leaf-nodes node revpath ->* node revpath)
    (print-index-leaf-node node revpath print-terms)))

(defmethod map-index-leaf-nodes (cc (node tree-index-internal-node) revpath)
  (prog->
    (tree-index-internal-node-variable-indexed-child-node node ->nonnil node)
    (map-index-leaf-nodes node (cons '? revpath) ->* node revpath)
    (funcall cc node revpath))
  (prog->
    (map-sparse-vector-with-indexes (tree-index-internal-node-constant-indexed-child-nodes node) ->* node const#)
    (map-index-leaf-nodes node (cons (symbol-numbered const#) revpath) ->* node revpath)
    (funcall cc node revpath))
  (prog->
    (map-sparse-vector-with-indexes (tree-index-internal-node-function-indexed-child-nodes node) ->* node fn#)
    (map-index-leaf-nodes node (cons (symbol-numbered fn#) revpath) ->* node revpath)
    (funcall cc node revpath)))

(defmethod map-index-leaf-nodes (cc (node tree-index-leaf-node) revpath)
  (funcall cc node revpath))

(defmethod print-index-leaf-node ((node tree-index-leaf-node) revpath print-terms)
  (with-standard-io-syntax2
    (prog->
      (tree-index-leaf-node-entries node -> entries)
      (format t "~%; Path ~A has ~:D entr~:@P." (reverse revpath) (sparse-vector-count entries))
      (when print-terms
        (map-sparse-vector entries :reverse t ->* entry)
        (format t "~%;    ")
        (print-term (index-entry-term entry))))))

;;; tree-index.lisp EOF
