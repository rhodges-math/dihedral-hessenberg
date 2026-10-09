import DihedralHessenberg.Dihedral.RankTwoRootVectors

/-! # Uniqueness of reduced words below maximal length -/

namespace Schubert.Dihedral

/-- Two reduced expressions of an element below maximal length are identical. -/
theorem reduced_words_eq (n : ℕ) (hthree : 3 ≤ n) (first second : List (Fin 2))
    (hfirst : IsReduced n hthree first) (hsecond : IsReduced n hthree second)
    (hprod : (coxeterSystem n hthree).wordProd first =
      (coxeterSystem n hthree).wordProd second) (hshort : first.length < n) :
    first = second := by
  induction first generalizing second with
  | nil =>
    have hlength := hsecond.eq
    rw [← hprod, CoxeterSystem.wordProd_nil, CoxeterSystem.length_one] at hlength
    exact (List.length_eq_zero_iff.mp hlength.symm).symm
  | cons generator tail ih =>
    have htail : IsReduced n hthree tail := by
      change (coxeterSystem n hthree).IsReduced tail
      simpa only [List.drop_succ_cons, List.drop_zero] using hfirst.drop 1
    cases second with
    | nil =>
      have hlength := hfirst.eq
      rw [hprod, CoxeterSystem.wordProd_nil, CoxeterSystem.length_one] at hlength
      simp only [List.length_cons] at hlength
      omega
    | cons other rest =>
      have hrest : IsReduced n hthree rest := by
        change (coxeterSystem n hthree).IsReduced rest
        simpa only [List.drop_succ_cons, List.drop_zero] using hsecond.drop 1
      have hlength : length n hthree ((coxeterSystem n hthree).wordProd
          (generator :: tail)) = tail.length + 1 := hfirst.eq
      have hpositive : 0 < length n hthree ((coxeterSystem n hthree).wordProd
          (generator :: tail)) := by omega
      have hbound : length n hthree ((coxeterSystem n hthree).wordProd
          (generator :: tail)) < n := by simpa only [hlength, List.length_cons] using hshort
      obtain ⟨simple, _, hunique⟩ := existsUnique_simple_left_descent n hthree
        ((coxeterSystem n hthree).wordProd (generator :: tail)) hpositive hbound
      have hdesc : length n hthree (simpleReflection n generator *
          (coxeterSystem n hthree).wordProd (generator :: tail)) + 1 =
            length n hthree ((coxeterSystem n hthree).wordProd (generator :: tail)) := by
        rw [CoxeterSystem.wordProd_cons, ← coxeterSystem_simple n hthree,
          CoxeterSystem.simple_mul_simple_cancel_left]
        change (coxeterSystem n hthree).length _ + 1 = _
        rw [htail.eq]
        exact hlength.symm
      have hother : length n hthree (simpleReflection n other *
          (coxeterSystem n hthree).wordProd (generator :: tail)) + 1 =
            length n hthree ((coxeterSystem n hthree).wordProd (generator :: tail)) := by
        rw [hprod, CoxeterSystem.wordProd_cons, ← coxeterSystem_simple n hthree,
          CoxeterSystem.simple_mul_simple_cancel_left]
        change (coxeterSystem n hthree).length _ + 1 =
          (coxeterSystem n hthree).length ((coxeterSystem n hthree).wordProd (other :: rest))
        rw [hrest.eq, hsecond.eq]
        rfl
      have hgenerators : generator = other := (hunique generator hdesc).trans
        (hunique other hother).symm
      subst other
      have htails : (coxeterSystem n hthree).wordProd tail =
          (coxeterSystem n hthree).wordProd rest := by
        rw [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons] at hprod
        exact mul_left_cancel hprod
      exact congrArg (List.cons generator) (ih rest htail hrest htails (by
        simp only [List.length_cons] at hshort
        omega))

/-- Every element of length less than the maximum has a unique reduced expression. -/
theorem unique_reduced_word (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (hshort : length n hthree element < n) :
    ∃! word : List (Fin 2), IsReduced n hthree word ∧
      (coxeterSystem n hthree).wordProd word = element := by
  obtain ⟨word, hreduced, hprod⟩ := (coxeterSystem n hthree).exists_isReduced element
  refine ⟨word, ⟨hreduced, hprod.symm⟩, ?_⟩
  intro other hother
  apply reduced_words_eq n hthree other word hother.1 hreduced
  · exact hother.2.trans hprod
  · rw [← hother.1.eq, hother.2]
    exact hshort


private theorem reduced_cons_eq (n : ℕ) (hthree : 3 ≤ n) (generator : Fin 2)
    (first second : List (Fin 2)) (hfirst : IsReduced n hthree (generator :: first))
    (hsecond : IsReduced n hthree (generator :: second))
    (hprod : (coxeterSystem n hthree).wordProd (generator :: first) =
      (coxeterSystem n hthree).wordProd (generator :: second)) (hshort : first.length < n) :
    generator :: first = generator :: second := by
  have htail : IsReduced n hthree first := by
    change (coxeterSystem n hthree).IsReduced first
    simpa only [List.drop_succ_cons, List.drop_zero] using hfirst.drop 1
  have hrest : IsReduced n hthree second := by
    change (coxeterSystem n hthree).IsReduced second
    simpa only [List.drop_succ_cons, List.drop_zero] using hsecond.drop 1
  rw [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons] at hprod
  exact congrArg (List.cons generator)
    (reduced_words_eq n hthree first second htail hrest (mul_left_cancel hprod) hshort)

/-- The longest element has exactly the two alternating reduced expressions. -/
theorem longest_reduced_words (n : ℕ) (hthree : 3 ≤ n) (word : List (Fin 2)) :
    (IsReduced n hthree word ∧ (coxeterSystem n hthree).wordProd word =
      longestElement n hthree) ↔
        word = CoxeterSystem.alternatingWord 0 1 n ∨
          word = CoxeterSystem.alternatingWord 1 0 n := by
  have hzero := alternatingWord_isReduced n hthree 0 1 (by decide) n le_rfl
  have hone := alternatingWord_isReduced n hthree 1 0 (by decide) n le_rfl
  have htop : length n hthree (longestElement n hthree) = n :=
    (length_eq_longest n hthree _).mpr rfl
  have hprod : (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 1 0 n) =
      longestElement n hthree := (alternatingWord_top_wordProd_eq n hthree).symm
  have hzero_head : CoxeterSystem.alternatingWord (0 : Fin 2) 1 n =
      (if Even (n - 1) then 1 else 0) :: CoxeterSystem.alternatingWord 0 1 (n - 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      CoxeterSystem.alternatingWord_succ' (0 : Fin 2) 1 (n - 1)
  have hone_head : CoxeterSystem.alternatingWord (1 : Fin 2) 0 n =
      (if Even (n - 1) then 0 else 1) :: CoxeterSystem.alternatingWord 1 0 (n - 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      CoxeterSystem.alternatingWord_succ' (1 : Fin 2) 0 (n - 1)
  constructor
  · rintro ⟨hreduced, hword⟩
    have hsize : word.length = n := by rw [← hreduced.eq, hword]; exact htop
    cases word with
    | nil => simp only [List.length_nil] at hsize; omega
    | cons generator tail =>
      have hshort : tail.length < n := by simp only [List.length_cons] at hsize; omega
      by_cases heven : Even (n - 1)
      · simp only [ite_eq_left heven] at hzero_head hone_head
        fin_cases generator
        · right
          rw [hone_head] at hone hprod ⊢
          exact reduced_cons_eq n hthree 0 tail _ hreduced hone (hword.trans hprod.symm) hshort
        · left
          rw [hzero_head] at hzero ⊢
          have hzero_prod : (coxeterSystem n hthree).wordProd
              (1 :: CoxeterSystem.alternatingWord 0 1 (n - 1)) = longestElement n hthree := by
            rw [← hzero_head]; rfl
          exact reduced_cons_eq n hthree 1 tail _ hreduced hzero
            (hword.trans hzero_prod.symm) hshort
      · simp only [ite_eq_right heven] at hzero_head hone_head
        fin_cases generator
        · left
          rw [hzero_head] at hzero ⊢
          have hzero_prod : (coxeterSystem n hthree).wordProd
              (0 :: CoxeterSystem.alternatingWord 0 1 (n - 1)) = longestElement n hthree := by
            rw [← hzero_head]; rfl
          exact reduced_cons_eq n hthree 0 tail _ hreduced hzero
            (hword.trans hzero_prod.symm) hshort
        · right
          rw [hone_head] at hone hprod ⊢
          exact reduced_cons_eq n hthree 1 tail _ hreduced hone (hword.trans hprod.symm) hshort
  · rintro (rfl | rfl)
    · exact ⟨hzero, rfl⟩
    · exact ⟨hone, hprod⟩


/-- Every reduced expression is alternating in one of the two simple orientations. -/
theorem reduced_word_alternating (n : ℕ) (hthree : 3 ≤ n) (word : List (Fin 2))
    (hreduced : IsReduced n hthree word) :
    word = CoxeterSystem.alternatingWord 0 1 word.length ∨
      word = CoxeterSystem.alternatingWord 1 0 word.length := by
  have hlength : length n hthree ((coxeterSystem n hthree).wordProd word) = word.length :=
    hreduced.eq
  have hbound : word.length ≤ n := by
    rw [← hlength]
    exact length_le_polygon_parameter n hthree _
  by_cases hshort : word.length < n
  · obtain ⟨first, second, hne, hprod⟩ := exists_alternatingWord_length n hthree
      ((coxeterSystem n hthree).wordProd word)
    rw [hlength] at hprod
    have halternating := alternatingWord_isReduced n hthree first second hne word.length hbound
    have heq := reduced_words_eq n hthree word _ hreduced halternating hprod.symm hshort
    fin_cases first <;> fin_cases second
    · exact (hne rfl).elim
    · exact Or.inl heq
    · exact Or.inr heq
    · exact (hne rfl).elim
  · have hsize : word.length = n := by omega
    rw [hsize]
    apply (longest_reduced_words n hthree word).mp
    refine ⟨hreduced, (length_eq_longest n hthree _).mp ?_⟩
    exact hlength.trans hsize

/-- Every element other than the named longest element has a unique reduced expression. -/
theorem unique_reduced_of_ne_longest (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (hne : element ≠ longestElement n hthree) :
    ∃! word : List (Fin 2), IsReduced n hthree word ∧
      (coxeterSystem n hthree).wordProd word = element := by
  apply unique_reduced_word n hthree element
  have hbound := length_le_polygon_parameter n hthree element
  have hnot : length n hthree element ≠ n := fun heq =>
    hne ((length_eq_longest n hthree element).mp heq)
  omega


/-- The two nonempty alternating expressions have different initial letters. -/
theorem alternating_words_ne (size : ℕ) (hpositive : 0 < size) :
    CoxeterSystem.alternatingWord (0 : Fin 2) 1 size ≠
      CoxeterSystem.alternatingWord 1 0 size := by
  cases size with
  | zero => omega
  | succ size =>
    intro heq
    rw [CoxeterSystem.alternatingWord_succ', CoxeterSystem.alternatingWord_succ'] at heq
    by_cases heven : Even size <;> simp only [heven, ↓reduceIte, List.cons.injEq] at heq <;>
      exact (by decide : (1 : Fin 2) ≠ 0) (by tauto)

end Schubert.Dihedral
