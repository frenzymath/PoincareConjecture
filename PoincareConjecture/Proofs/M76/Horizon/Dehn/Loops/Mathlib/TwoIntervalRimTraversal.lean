import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.SquareTwoIntervalNormalization
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.MarkedIntervalHomotopy
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

theorem exists_marked_two_interval_rim_traversal
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] {Q U V : Set E} {a b : E} {Z : Set X}
    (hab : a ≠ b) (hUV : U ∩ V = {a, b}) (hcover : U ∪ V = Q)
    (hV : IsFinitePLBallPair ℝ V {a, b})
    (p : I01 ≃ₜ U) (hp : p.IsFinitePL)
    (hp0 : (p (0 : unitInterval) : E) = a) (hp1 : (p (1 : unitInterval) : E) = b)
    (f : E → X) (hf : ContinuousOn f Q) (hfZ : MapsTo f Q Z)
    (P : Path a b) (hP : ∀ t, P t ∈ V) {x y : Z} (A B : Path x y)
    (hA : ∀ t : I01, (A t : X) = f (p t))
    (hB : ∀ t : I01, (B t : X) = f (P t)) :
    ∃ (H : Q2 ≃ₜ Q) (R : Path x x), H.IsFinitePL ∧
      (H squareRimBase : E) = a ∧
      (∀ t : I01, (R t : X) = f (H (squareRimLoop t))) ∧
      R.Homotopic (A.trans B.symm) := by
  obtain ⟨q, hq, hq0, hq1⟩ := hV.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨G, hG, _, _, hbase, hloop⟩ :=
    exists_squareRim_two_interval_normalization hab hUV p q hp hq hp0 hp1 hq0 hq1
  let H : Q2 ≃ₜ Q := (Homeomorph.setCongr rfl).trans
    (G.trans (Homeomorph.setCongr hcover))
  have hH : H.IsFinitePL := hG.setCongr rfl hcover
  have hVQ : V ⊆ Q := subset_union_right.trans hcover.subset
  have hx : (x : X) = f a := by simpa only [Path.source] using hB 0
  have hy : (y : X) = f b := by simpa only [Path.target] using hB 1
  let C : Path x y :=
    { toFun t := ⟨f (q t), hfZ (hVQ (q t).property)⟩
      continuous_toFun := (hf.comp_continuous
        (continuous_subtype_val.comp q.continuous) (fun t ↦ hVQ (q t).property)).subtype_mk _
      source' := Subtype.ext ((congrArg f hq0).trans hx.symm)
      target' := Subtype.ext ((congrArg f hq1).trans hy.symm) }
  have hhom : C.Homotopic B :=
    marked_interval_paths_homotopic q f (hf.mono hVQ) (hfZ.mono hVQ Subset.rfl)
      ((intervalChartPath q).cast hq0.symm hq1.symm) P
      (fun t ↦ (q t).property) hP C B (fun _ ↦ rfl) hB
  have hval (t : I01) : ((A.trans C.symm) t : X) = f (H (squareRimLoop t)) := by
    have hv := congrArg (fun r : Path a a ↦ r t) hloop
    change (G (squareRimLoop t) : E) =
      (((intervalChartPath p).cast hp0.symm hp1.symm).trans
        ((intervalChartPath q).cast hq0.symm hq1.symm).symm) t at hv
    change ((A.trans C.symm) t : X) = f (G (squareRimLoop t))
    rw [hv]
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs
    · exact hA _
    · rfl
  exact ⟨H, A.trans C.symm, hH, hbase, hval, (Path.Homotopic.refl A).hcomp hhom.symm₂⟩

end PoincareConjecture.M76.Dehn
