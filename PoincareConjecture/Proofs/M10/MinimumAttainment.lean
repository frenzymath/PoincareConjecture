import PoincareConjecture.Proofs.M10.ReducedLengthSublevel
import PoincareConjecture.Proofs.M10.CompactSublevelMinimum
import PoincareConjecture.Proofs.M10.Continuity










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

omit [T3Space M] in

theorem exists_uniform_reducedLength_comparator
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    {a b : ℝ} (ha : 0 < a) (hbmax : b < τmax) :
    ∃ L : ℝ, ∀ τ ∈ Icc a b, ∃ q : M, reducedLength F T p q τ ≤ L := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let Z : TangentSpace (𝓡 n) p := 0
  let A := fun τ : ℝ ↦ G.toLExponentialFamily.action Z τ / (2 * Real.sqrt τ)
  have hA : ContinuousOn A (Icc a b) := by
    dsimp only [A]
    refine ContinuousOn.div ?_ (by fun_prop) ?_
    · apply G.action_smooth.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
      intro τ hτ
      exact ⟨mem_univ _, ha.trans_le hτ.1, hτ.2.trans_lt hbmax⟩
    · intro τ hτ
      exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        (Real.sqrt_pos.mpr (ha.trans_le hτ.1)).ne'
  obtain ⟨L, hLbound⟩ := isCompact_Icc.bddAbove_image hA
  refine ⟨L, ?_⟩
  intro τ hτ
  refine ⟨G.gamma Z τ, (reducedLength_le_normalized_action hL G Z τ
    (ha.trans_le hτ.1) (hτ.2.trans_lt hbmax)).trans ?_⟩
  exact hLbound (mem_image_of_mem A hτ)


theorem reducedLength_infimum_on_compact_time
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbmax : b < τmax) :
    ContinuousOn (fun τ : ℝ ↦ sInf (range (fun q ↦ reducedLength F T p q τ))) (Icc a b) ∧
      ∀ τ ∈ Icc a b, ∃ q : M,
        reducedLength F T p q τ = sInf (range (fun y ↦ reducedLength F T p y τ)) := by
  obtain ⟨L, hcomp⟩ := exists_uniform_reducedLength_comparator hL G ha hbmax
  obtain ⟨K, hK, hsub⟩ := exists_compact_reducedLength_sublevel hL G hwindow hcurvature
    (ha.trans_le hab) hbmax L
  have hf : Continuous (fun z : Icc a b × M ↦ reducedLength F T p z.2 z.1) :=
    (reducedLength_continuousOn hL hDifferential p).comp_continuous
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
      (fun z ↦ ⟨mem_univ _, ha.trans_le z.1.property.1, z.1.property.2.trans_lt hbmax⟩)
  constructor
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_sInf_of_compact_sublevels
      (f := fun τ : Icc a b ↦ fun q ↦ reducedLength F T p q τ) hf hK
      (fun τ q hq ↦ hsub τ (ha.trans_le τ.property.1) τ.property.2 q hq)
      (fun τ ↦ hcomp τ τ.property)
  · intro τ hτ
    have hslice : Continuous (fun q : M ↦ reducedLength F T p q τ) :=
      (reducedLength_continuousOn hL hDifferential p).comp_continuous
        (continuous_id.prodMk continuous_const)
        (fun _ ↦ ⟨mem_univ _, ha.trans_le hτ.1, hτ.2.trans_lt hbmax⟩)
    obtain ⟨q, _, _, hq⟩ := exists_global_minimum_of_compact_sublevel hslice hK
      (hsub τ (ha.trans_le hτ.1) hτ.2) (hcomp τ hτ)
    exact ⟨q, hq⟩


theorem reducedLength_minimum_data
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T)) :
    ContinuousOn (fun τ : ℝ ↦ sInf (range (fun q ↦ reducedLength F T p q τ))) (Ioo 0 τmax) ∧
      ∀ τ ∈ Ioo 0 τmax, ∃ q : M,
        reducedLength F T p q τ = sInf (range (fun y ↦ reducedLength F T p y τ)) := by
  constructor
  · intro τ hτ
    have hc := (reducedLength_infimum_on_compact_time hL G hDifferential hwindow hcurvature
      (a := τ / 2) (b := (τ + τmax) / 2) (by linarith [hτ.1])
      (by linarith [hτ.1, hτ.2]) (by linarith [hτ.2])).1
    exact (hc.continuousAt (Icc_mem_nhds (by linarith [hτ.1])
      (by linarith [hτ.2]))).continuousWithinAt
  · intro τ hτ
    exact (reducedLength_infimum_on_compact_time hL G hDifferential hwindow hcurvature
      hτ.1 le_rfl hτ.2).2 τ ⟨le_rfl, le_rfl⟩

end PoincareConjecture.M10
