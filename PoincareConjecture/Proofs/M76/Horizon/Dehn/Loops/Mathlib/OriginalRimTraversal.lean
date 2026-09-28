import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalRimComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalStripEndPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.TwoIntervalRimTraversal










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1




theorem exists_original_rim_traversal_of_exterior_paths
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] {S Q A M C : Set E} (hS : IsFinitePLBallPair P2 S Q)
    (c : Bool → P2 → E) (hc : ∀ i, ContinuousOn (c i) source)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1))
    (hAM : Disjoint A M) (hAC : Disjoint A C)
    (hcover : ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = S)
    (s0 s1 : Bool)
    (h0A : (c false '' source) ∩ A = c false '' arm (farArmParameter (!s0)))
    (hA1 : Disjoint A (c true '' source))
    (hAI : IsFinitePLBallPair ℝ (A ∩ Q)
      {c false (0, farArmParameter (!s0)), c false (1, farArmParameter (!s0))})
    (hab : c false (0, farArmParameter (!s0)) ≠ c false (1, farArmParameter (!s0)))
    (pA : I01 ≃ₜ (A ∩ Q : Set E)) (hpA : pA.IsFinitePL)
    (hpA0 : (pA (0 : unitInterval) : E) = c false (0, farArmParameter (!s0)))
    (hpA1 : (pA (1 : unitInterval) : E) = c false (1, farArmParameter (!s0)))
    (s t : unitInterval) (hs : (s : ℝ) = 0 ∨ (s : ℝ) = 1)
    (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    (L : Path (c false (0, farArmParameter s0)) (c true (s, farArmParameter s1)))
    (K : Path (c true (s, farArmParameter (!s1))) (c true (t, farArmParameter (!s1))))
    (N : Path (c true (t, farArmParameter s1)) (c false (1, farArmParameter s0)))
    (hL : ∀ r, L r ∈ M ∩ Q) (hK : ∀ r, K r ∈ C ∩ Q) (hN : ∀ r, N r ∈ M ∩ Q)
    {Z : Set X} (f : E → X) (hf : ContinuousOn f Q) (hfZ : MapsTo f Q Z)
    {x y : Z} (a : Path x y) (ha : ∀ r : I01, (a r : X) = f (pA r)) :
    let P := ((((((originalStripEndPath (c false) (hc false) 0 s0).trans L).trans
      (originalStripEndPath (c true) (hc true) s s1).symm).trans K).trans
      (originalStripEndPath (c true) (hc true) t s1)).trans N).trans
      (originalStripEndPath (c false) (hc false) 1 s0).symm
    ∃ (H : Q2 ≃ₜ Q) (R : Path x x) (B : Path x y), H.IsFinitePL ∧
      (H squareRimBase : E) = c false (0, farArmParameter (!s0)) ∧
      (∀ r : I01, (B r : X) = f (P r)) ∧
      (∀ r : I01, (R r : X) = f (H (squareRimLoop r))) ∧
      R.Homotopic (a.trans B.symm) := by
  let V := ((M ∩ Q) ∪ (C ∩ Q)) ∪ ((c false '' stripEnds) ∪ (c true '' stripEnds))
  have hfar : farArmParameter (!s0) ∈ Icc (-1 : ℝ) 1 := by
    cases s0 <;> norm_num [farArmParameter]
  obtain ⟨hV, hUV, hi⟩ := original_rim_complement_is_interval hS c hcQ hAM hAC
    hcover (farArmParameter (!s0)) hfar h0A hA1 hAI hab
  have hVQ : V ⊆ Q := subset_union_right.trans hUV.subset
  let P := ((((((originalStripEndPath (c false) (hc false) 0 s0).trans L).trans
    (originalStripEndPath (c true) (hc true) s s1).symm).trans K).trans
    (originalStripEndPath (c true) (hc true) t s1)).trans N).trans
    (originalStripEndPath (c false) (hc false) 1 s0).symm
  have htrans {a b d : E} (p : Path a b) (q : Path b d)
      (hp : ∀ r, p r ∈ V) (hq : ∀ r, q r ∈ V) : ∀ r, p.trans q r ∈ V := by
    intro r
    rw [Path.trans_apply]
    split_ifs
    · exact hp _
    · exact hq _
  have hEnd0 (v : unitInterval) (hv : (v : ℝ) = 0 ∨ (v : ℝ) = 1)
      (r : unitInterval) : originalStripEndPath (c false) (hc false) v s0 r ∈ V :=
    Or.inr (Or.inl (originalStripEndPath_mem_ends (c false) (hc false) v s0 hv r))
  have hEnd1 (v : unitInterval) (hv : (v : ℝ) = 0 ∨ (v : ℝ) = 1)
      (r : unitInterval) : originalStripEndPath (c true) (hc true) v s1 r ∈ V :=
    Or.inr (Or.inr (originalStripEndPath_mem_ends (c true) (hc true) v s1 hv r))
  have hPV : ∀ r, P r ∈ V :=
    htrans _ _ (htrans _ _ (htrans _ _ (htrans _ _ (htrans _ _ (htrans _ _
      (hEnd0 0 (by simp)) (fun r ↦ Or.inl (Or.inl (hL r))))
      (fun r ↦ hEnd1 s hs (unitInterval.symm r))) (fun r ↦ Or.inl (Or.inr (hK r))))
      (hEnd1 t ht)) (fun r ↦ Or.inl (Or.inl (hN r))))
      (fun r ↦ hEnd0 1 (by simp) (unitInterval.symm r))
  have hx : (x : X) = f (c false (0, farArmParameter (!s0))) := by
    simpa only [Path.source, hpA0] using ha 0
  have hy : (y : X) = f (c false (1, farArmParameter (!s0))) := by
    simpa only [Path.target, hpA1] using ha 1
  let B : Path x y :=
    { toFun r := ⟨f (P r), hfZ (hVQ (hPV r))⟩
      continuous_toFun := (hf.comp_continuous P.continuous
        (fun r ↦ hVQ (hPV r))).subtype_mk _
      source' := Subtype.ext ((congrArg f P.source).trans hx.symm)
      target' := Subtype.ext ((congrArg f P.target).trans hy.symm) }
  obtain ⟨H, R, hH, hbase, hR, hhom⟩ := exists_marked_two_interval_rim_traversal
    hab hi hUV hV pA hpA hpA0 hpA1 f hf hfZ P hPV a B ha (fun _ ↦ rfl)
  exact ⟨H, R, B, hH, hbase, fun _ ↦ rfl, hR, hhom⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
