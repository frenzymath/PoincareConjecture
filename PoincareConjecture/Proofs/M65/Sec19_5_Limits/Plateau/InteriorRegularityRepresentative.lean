import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalHolder
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

open Set Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65LocalWeakMap

theorem exists_embedded_holder_representative
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hU : IsOpen U) (hmin : M65LocallyMinimizesEnergy g F) :
    ∃ v : LoopPlane → EuclideanSpace ℝ (Fin N), ContinuousOn v U ∧
      (v =ᵐ[volume.restrict U] fun z => e (F.value z)) ∧
      ∀ p ∈ U, ∃ r β H : ℝ, 0 < r ∧ 0 < β ∧ β < 1 ∧ 0 < H ∧
        ball p r ⊆ U ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
          ‖v y - v x‖ ≤ H * dist y x ^ β := by
  classical
  have hlocal (p : U) : ∃ (r β H : ℝ) (v : LoopPlane → EuclideanSpace ℝ (Fin N)),
      0 < r ∧ 0 < β ∧ β < 1 ∧ 0 < H ∧ ball p.1 r ⊆ U ∧
      ContinuousOn v (ball p.1 r) ∧
      (v =ᵐ[volume.restrict (ball p.1 r)] fun z => e (F.value z)) ∧
      ∀ x ∈ ball p.1 r, ∀ y ∈ ball p.1 r,
        ‖v y - v x‖ ≤ H * dist y x ^ β := by
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds p.2)
    obtain ⟨v, β, H, hβ, hβ1, hH, hv, hAE, hholder⟩ :=
      F.local_holder_of_minimum g he hinj hemb compact hU hmin p.1 hR hRU
    refine ⟨R / 8, β, H, v, by positivity, hβ, hβ1, hH, ?_,
      hv.mono ball_subset_closedBall,
      ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hAE, ?_⟩
    · exact ball_subset_closedBall.trans
        ((closedBall_subset_closedBall (by linarith)).trans hRU)
    · intro x hx y hy
      exact hholder x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
  choose r β H v hr hβ hβ1 hH hsub hv hAE hholder using hlocal
  have hoverlap (p q : U) : EqOn (v p) (v q) (ball p.1 (r p) ∩ ball q.1 (r q)) := by
    have hp : v p =ᵐ[volume.restrict (ball p.1 (r p) ∩ ball q.1 (r q))]
        fun z => e (F.value z) :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hAE p)
    have hq : v q =ᵐ[volume.restrict (ball p.1 (r p) ∩ ball q.1 (r q))]
        fun z => e (F.value z) :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hAE q)
    exact Measure.eqOn_open_of_ae_eq (hp.trans hq.symm)
      (isOpen_ball.inter isOpen_ball) ((hv p).mono inter_subset_left)
      ((hv q).mono inter_subset_right)
  let V : LoopPlane → EuclideanSpace ℝ (Fin N) :=
    fun z => if hz : z ∈ U then v ⟨z, hz⟩ z else e (F.value z)
  have heq (p : U) : EqOn V (v p) (ball p.1 (r p)) := by
    intro z hz
    have hzU := hsub p hz
    change (if hz : z ∈ U then v ⟨z, hz⟩ z else e (F.value z)) = v p z
    rw [dif_pos hzU]
    exact hoverlap ⟨z, hzU⟩ p ⟨mem_ball_self (hr ⟨z, hzU⟩), hz⟩
  have hVc : ContinuousOn V U := by
    intro z hz
    let p : U := ⟨z, hz⟩
    have hp : z ∈ ball p.1 (r p) := mem_ball_self (hr p)
    have hc := (hv p z hp).continuousAt (isOpen_ball.mem_nhds hp)
    apply ContinuousAt.continuousWithinAt
    exact hc.congr_of_eventuallyEq ((heq p).eventuallyEq_of_mem (isOpen_ball.mem_nhds hp))
  have hcover : (⋃ p : U, ball p.1 (r p)) = U := by
    apply Subset.antisymm
    · exact iUnion_subset hsub
    · intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr ⟨z, hz⟩)⟩
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable
    (fun p : U => ball p.1 (r p)) (fun _ => isOpen_ball)
  have hVAE : V =ᵐ[volume.restrict U] fun z => e (F.value z) := by
    have hlocalAE : V =ᵐ[volume.restrict (⋃ p ∈ T, ball p.1 (r p))]
        fun z => e (F.value z) := by
      apply (ae_eq_restrict_biUnion_iff _ hT _ _).mpr
      intro p _
      filter_upwards [hAE p, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzp
      exact (heq p hzp).trans hz
    have hmu : volume.restrict (⋃ p ∈ T, ball p.1 (r p)) = volume.restrict U :=
      congrArg (fun s : Set LoopPlane => volume.restrict s) (hTU.trans hcover)
    rwa [hmu] at hlocalAE
  refine ⟨V, hVc, hVAE, ?_⟩
  intro p hp
  let q : U := ⟨p, hp⟩
  refine ⟨r q, β q, H q, hr q, hβ q, hβ1 q, hH q, hsub q, ?_⟩
  intro x hx y hy
  rw [heq q hx, heq q hy]
  exact hholder q x hx y hy

theorem exists_holder_representative
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hU : IsOpen U) (hmin : M65LocallyMinimizesEnergy g F) :
    ∃ q : LoopPlane → M, ContinuousOn q U ∧
      (q =ᵐ[volume.restrict U] F.value) ∧
      ∀ p ∈ U, ∃ r β H : ℝ, 0 < r ∧ 0 < β ∧ β < 1 ∧ 0 < H ∧
        ball p r ⊆ U ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
          ‖e (q y) - e (q x)‖ ≤ H * dist y x ^ β := by
  classical
  obtain ⟨V, hVc, hAE, hholder⟩ :=
    F.exists_embedded_holder_representative g he hinj hemb compact hU hmin
  have hclosed : IsClosed (range e) := by
    simpa only [image_univ] using (compact.image hemb.continuous).isClosed
  have hnonempty : (range e).Nonempty := ⟨e (F.value 0), mem_range_self _⟩
  have hdistAE : (fun z => infDist (V z) (range e)) =ᵐ[volume.restrict U] fun _ => 0 := by
    filter_upwards [hAE] with z hz
    rw [hz]
    exact infDist_zero_of_mem (mem_range_self _)
  have hdist := Measure.eqOn_open_of_ae_eq hdistAE hU
    ((continuous_infDist_pt (range e)).comp_continuousOn hVc) continuousOn_const
  have hmem (z : LoopPlane) (hz : z ∈ U) : V z ∈ range e :=
    (hclosed.mem_iff_infDist_zero hnonempty).mpr (hdist hz)
  let : Nonempty M := ⟨F.value 0⟩
  let q : LoopPlane → M := fun z => Function.invFun e (V z)
  have heq : EqOn (e ∘ q) V U := by
    intro z hz
    obtain ⟨p, hp⟩ := hmem z hz
    change e (Function.invFun e (V z)) = V z
    rw [← hp]
    exact Function.apply_invFun_apply
  refine ⟨q, hemb.isInducing.continuousOn_iff.mpr (hVc.congr heq), ?_, ?_⟩
  · filter_upwards [hAE, ae_restrict_mem hU.measurableSet] with z hz hzU
    exact hemb.injective ((heq hzU).trans hz)
  · intro p hp
    obtain ⟨r, β, H, hr, hβ, hβ1, hH, hsub, hh⟩ := hholder p hp
    refine ⟨r, β, H, hr, hβ, hβ1, hH, hsub, ?_⟩
    intro x hx y hy
    change ‖(e ∘ q) y - (e ∘ q) x‖ ≤ _
    rw [heq (hsub hx), heq (hsub hy)]
    exact hh x hx y hy

end PoincareConjecture.M65LocalWeakMap
