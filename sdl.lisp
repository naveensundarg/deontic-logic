
;;; The syntax of Standard Deontic Logic axiomatized in FOL.
;;; http://plato.stanford.edu/entries/logic-deontic/#2.1
;;; Naveen Sundar Govindarajulu,
;;; RAIR Lab
;;; Rensselaer Polytechnic Institute
;;; Summer 2012
;;; Changed: December 2012


;;; SDL \vdash represented by holds in FOL. 
;;; Axioms become unconditional holds statements. 

(in-package :snark-user)


(defparameter *A2*
  '(forall ((?p proposition) (?q proposition))
    (holds 
     (implies!
      (Ob (implies! ?p ?q))
      (implies! 
        (Ob ?p)
	(Ob ?q))))))

(defparameter *A3*
  '(forall ((?p proposition))
    (holds 
     (implies!
      (Ob ?p)
      (not! (Ob (not! ?p)))))))

(defparameter *R1*
  '(forall ((?p proposition) (?q proposition)) 
    (implies 
     (and (holds ?p) (holds (implies! ?p ?q))) 
     (holds ?q))))

(defparameter *R2*
  '(forall ((?p proposition)) 
    (implies 
     (holds ?p) 
     (holds (Ob ?p)))))

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

(defparameter *ob-rm* 
  '(forall ((?p proposition) (?q proposition)) 
    (implies 
     (holds (implies! p q)) 
     (holds (implies! (Ob p) (Ob q))))))


(defparameter *ob-re* 
  '(forall ((?p proposition) (?q proposition)) 
    (implies 
     (holds (iff! p q)) 
     (holds (iff! (Ob p) (Ob q))))))

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


(defun prove-r-sdl (w &optional (premises nil))
  (snark:initialize)
  (declare-sort 'proposition)
  (declare-constant 's :sort 'proposition)
  (declare-constant 'a :sort 'proposition)
  (declare-constant 'search-and-rescue-mode :sort 'proposition)
  (declare-constant 'transportation-mode :sort 'proposition)

  (declare-relation 'holds 1 :sort '(proposition))
  (declare-function 'and! 2 :sort '(proposition proposition proposition))
  (declare-function 'or! 2 :sort '(proposition proposition proposition))
  (declare-function 'implies! 2 :sort '(proposition proposition proposition))
  (declare-function 'iff! 2 :sort '(proposition proposition proposition))
  (declare-function 'not! 1 :sort '(proposition  proposition))
  (declare-function 'Ob 1 :sort '(proposition  proposition))
  ;(use-resolution t)
  ;(use-paramodulation t)
  (use-hyperresolution t)
  (mapcar #'assert 
	  (list *not!* *and!* *or!* *iff!* *implies!*
		*A2* *A3* *R1* *R2*
		 ;*ob-rm* *ob-re* *ded*
		))
  (mapcar #'assert premises)
  (prove w))





;;; Handbook of philosphical logic