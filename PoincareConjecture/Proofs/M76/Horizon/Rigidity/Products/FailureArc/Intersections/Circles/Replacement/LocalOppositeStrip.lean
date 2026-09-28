import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.AnnularCollarSide








set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_local_opposite_strip_avoiding_surface
    {X A B : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace B] [CompactSpace B] [PreconnectedSpace B]
    {K S O : Set X} (C : (A × I) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K)
    (hzero : ∀ z, (C z : X) ∈ S ↔ (z.2 : ℝ) = 0)
    (p : B × J → X) (hp : Continuous p)
    (hpO : ∀ b, p (b,⟨0,by norm_num⟩) ∈ O)
    (hproper : ∀ z, p z ∈ S ↔ (z.2 : ℝ) = 0)
    {Q : Set A} (hQ : IsCompact Q) {Z D : Set X} (hZ : IsClosed Z)
    (hQZ : ∀ q ∈ Q, (C (q,⟨0,by norm_num⟩) : X) ∉ Z)
    (hD : D ⊆ S ∪ range p ∪ Z) :
    ∃ (ε : ℝ) (positive : Bool), 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ (q : A) (_hq : q ∈ Q) (t : I),
        (if positive then (t : ℝ) ∈ Ico (-ε) 0 else (t : ℝ) ∈ Ioc 0 ε) →
        (C (q,t) : X) ∉ D := by
  obtain ⟨a,δ,positive,_,_,hδ,hδhalf,_,_,havoid⟩ :=
    exists_attached_annulus_opposite_collar_half C hO hOK hzero p hp hpO hproper
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let f : Q × I → X := fun z => C (z.1,z.2)
  have hf : Continuous f := continuous_subtype_val.comp (C.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  obtain ⟨r,hr,_,hthin⟩ := hf.exists_closed_strip_subset hZ.isOpen_compl
    (fun q => hQZ q q.property)
  let ε := min δ r
  have hε : 0 < ε := lt_min hδ hr
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεr : ε ≤ r := min_le_right _ _
  refine ⟨ε,positive,hε,hεδ.trans hδhalf,?_⟩
  intro q hq t ht hmem
  have htime : |(t : ℝ)| ≤ ε := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at ht ⊢ <;>
      exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have ht0 : (t : ℝ) ≠ 0 := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at ht ⊢ <;>
      linarith [ht.1,ht.2]
  rcases hD hmem with (hS | hp') | hZ'
  · exact ht0 ((hzero (q,t)).mp hS)
  · apply havoid (q,t) _ hp'
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at ht ⊢
    · exact ⟨ht.1,ht.2.trans hεδ⟩
    · exact ⟨(neg_le_neg hεδ).trans ht.1,ht.2⟩
  · exact hthin ⟨q,hq⟩ t (htime.trans hεr) hZ'

end PoincareConjecture.M76
