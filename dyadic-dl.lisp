
;;; The syntax of a dyadic deontic logic axiomatized in FOL.
;;; http://plato.stanford.edu/entries/logic-deontic/#2.1
;;;; See http://plato.stanford.edu/entries/logic-deontic/chisholm.html
;;; Naveen Sundar Govindarajulu,
;;; RAIR Lab
;;; Rensselaer Polytechnic Institute
;;; August 2012
;;; Changed: December 2012

;;;  \vdash represented by holds in FOL. 
;;; Axioms become unconditional holds statements. 


;;; Note the order of the arguments here for the ought operator
;;; is different from that given in the papers on the DCEC.
;;; In DCEC what is O(p,q) is given here as O(q,p). 


(in-package :snark-user)


(defparameter *A2*
  '(forall ((?p proposition) (?q proposition) (?r proposition))
    (holds 
     (implies!
      (Ob (implies! ?p ?q) ?r)
      (implies! 
        (Ob ?p ?r)
	(Ob ?q ?r))))))

(defparameter *A3*
  '(forall ((?p proposition) (?r proposition))
    (holds 
     (implies!
      (Ob ?p ?r)
      (not! (Ob (not! ?p) ?r))))))

(defparameter *A4*
  '(forall ((?p proposition))
    (holds (Ob  (or! ?p (not! ?p)) (or! ?p (not! ?p)))))) 

(defparameter *A5*
  '(forall ((?p proposition) (?q proposition))
    (holds (implies! (Ob ?q ?p) (Ob (and! ?p ?q) ?p)))))

(defparameter *def-pref*
  '(forall ((?p proposition) (?q proposition))
    (iff (holds (pref ?p ?q))
     (holds (not! (Ob (not! ?p) (or! ?p ?q)))))))

(defparameter *A6*
  '(forall ((?p proposition) (?q proposition) (?r proposition))
    (holds (implies! (and! (pref ?p ?q) (pref ?q ?r))
	    (pref ?p ?r)))))

(defparameter *R1*
  '(forall ((?p proposition) (?q proposition)) 
    (implies 
     (and (holds ?p) (holds (implies! ?p ?q))) 
     (holds ?q))))

(defparameter *R2*
  '(forall ((?p proposition) (?q proposition) (?r proposition)) 
    (implies 
     (holds (iff! ?p ?q)) 
     (holds  (iff! (Ob ?p ?r) (Ob ?q ?r))))))

(defparameter *R3*
  '(forall ((?p proposition) (?q proposition) (?r proposition)) 
    (implies 
     (holds (implies! ?p ?q)) 
     (holds  (implies! (Ob ?p ?r) (Ob ?q ?r))))))

(defparameter *not!*
  '(forall ((?p proposition))
    (iff
     (holds (not! ?p))
     (not (holds ?p)))))

(defparameter *or!*
  '(forall ((?p proposition) (?q proposition))
    (iff
     (holds (or! ?p ?q))
     (or (holds ?p) (holds ?q)))))

(defparameter *and!*
  '(forall ((?p proposition) (?q proposition))
    (iff
     (holds (and! ?p ?q))
     (and (holds ?p) (holds ?q)))))

(defparameter *implies!*
  '(forall ((?p proposition) (?q proposition))
    (iff
     (holds (implies! ?p ?q))
     (implies (holds ?p) (holds ?q)))))


(defparameter *iff!*
  '(forall ((?p proposition) (?q proposition))
    (iff
     (holds (iff! ?p ?q))
     (iff (holds ?p) (holds ?q)))))

(defparameter *ded* 
  '(forall ((?p proposition) (?q proposition)) 
    (iff 
     (implies 
      (holds ?p) 
      (holds ?q))
     (holds (implies! ?p ?q)))))

(defun test-pc (w)
  (snark:initialize)
  (use-hyperresolution t)
  (use-paramodulation t)
  (mapcar #'assert (list *not!* *and!* *or!* *iff!* *implies!*))
  (prove w))


(defun prove-d-dl (w &optional (premises nil))
  (snark:initialize)
  (declare-sort 'proposition)
  (declare-constant 's :sort 'proposition)
  (declare-constant 'a :sort 'proposition)
  (declare-constant 'search-and-rescue-mode :sort 'proposition)
  (declare-constant 'transportation-mode :sort 'proposition)
 (snark:run-time-limit 15)
  (declare-relation 'holds 1 :sort '(proposition))
  (declare-function 'and! 2 :sort '(proposition proposition proposition))
  (declare-function 'or! 2 :sort '(proposition proposition proposition))
  (declare-function 'implies! 2 :sort '(proposition proposition proposition))
  (declare-function 'iff! 2 :sort '(proposition proposition proposition))
  (declare-function 'not! 1 :sort '(proposition  proposition))
  (declare-function 'Ob 2 :sort '(proposition proposition proposition))
  (declare-function 'pref 2 :sort '(proposition proposition proposition))
  ;(use-resolution t)
  ;(use-paramodulation t)
  (use-hyperresolution t)
  (mapcar #'assert 
	  (list *not!* *and!* *or!* *iff!* *implies!*
		*def-pref* *A2* *A3* *A4* *A5* *A6* *R1* *R2* *R3* 
		 ;*ded*
		))
  (mapcar #'assert premises)
  (prove w))


;;; 
(defun chisholm-paradox-ddl ()
  (prove-d-dl 
   '(and P (not P)) 
   (list 
    '(holds (Ob transportation-mode (or! a (not! a)))) 
    '(holds (Ob (not! search-and-rescue-mode) transportation-mode )) 
    '(holds (implies! (not! transportation-mode) (Ob search-and-rescue-mode (or! a (not! a)))))
    '(holds (not! transportation-mode)))))

3
(defun scout-check ()
  (chisholm-paradox-ddl)
  (format t "~%=========================================~%")
  (format t "=========================================~%")
  (format t "=========================================~%")
  (format t "       Everything seems consistent now. Proceeding Further.                      ~%")
  (format t "=========================================~%")
  (format t "=========================================~%")
  (format t "=========================================~%")
  (force-output t)
  (say " Everything seems consistent now. Proceeding Further.!"))
;;; Handbook of philosphical logic