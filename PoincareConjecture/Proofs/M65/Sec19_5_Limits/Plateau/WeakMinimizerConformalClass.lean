import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformalTrace
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerClass












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal

universe u

namespace PoincareConjecture




theorem M65WeakCircleParameter.comp_homeomorph {β : C(LoopCircle, LoopCircle)}
    (hβ : M65WeakCircleParameter β) (H : LoopCircle ≃ₜ LoopCircle) :
    M65WeakCircleParameter (β.comp ⟨H, H.continuous⟩) := by
  let A := range (fun h : LoopCircle ≃ₜ LoopCircle =>
    (⟨h, h.continuous⟩ : C(LoopCircle, LoopCircle)))
  let T := fun f : C(LoopCircle, LoopCircle) => f.comp ⟨H, H.continuous⟩
  have hT : Continuous T := ContinuousMap.continuous_precomp ⟨H, H.continuous⟩
  have hh : T β ∈ closure (T '' A) := mem_closure_image hT.continuousAt hβ
  apply (closure_mono (show T '' A ⊆ A from ?_)) hh
  rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
  exact ⟨H.trans h, rfl⟩





theorem M65WeakCircleParameter.surjective {β : C(LoopCircle, LoopCircle)}
    (hβ : M65WeakCircleParameter β) : Function.Surjective β := by
  intro y
  by_contra hmiss
  have havoid : MapsTo β univ ({y}ᶜ : Set LoopCircle) := by
    intro x _ hx
    exact hmiss ⟨x, hx⟩
  have hn := ContinuousMap.eventually_mapsTo isCompact_univ
    (isClosed_singleton (x := y)).isOpen_compl havoid
  obtain ⟨f, hfn, hf⟩ := mem_closure_iff_nhds.mp hβ _ hn
  obtain ⟨H, rfl⟩ := hf
  exact hfn (mem_univ (H.symm y)) (H.apply_symm_apply y)

set_option maxHeartbeats 1600000 in






theorem m65WeakDisk_smooth_change
    {M : Type u} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (he : Continuous e) (hγ : Continuous γ) (F : M65WeakDisk e γ)
    (φ ψ : LoopPlane → LoopPlane)
    (hφ : ContDiff ℝ 1 φ) (hψ : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 ψ z)
    (hφdisk : MapsTo φ loopDiskSet loopDiskSet)
    (hψdisk : MapsTo ψ loopDiskSet loopDiskSet)
    (hφcircle : ∀ z, ‖z‖ = 1 → ‖φ z‖ = 1)
    (hψcircle : ∀ z, ‖z‖ = 1 → ‖ψ z‖ = 1)
    (hleft : ∀ z ∈ loopDiskSet, ψ (φ z) = z)
    (hright : ∀ z ∈ loopDiskSet, φ (ψ z) = z) :
    ∃ G : M65WeakDisk e γ, G.value = F.value ∘ φ ∧
      (∀ z : LoopCircle, G.parameter z = F.parameter ⟨φ z, hφcircle z z.property⟩) ∧
      ∀ i, G.derivative i =ᵐ[volume.restrict loopDiskSet] fun z =>
        ∑ j : Fin 2, (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j •
          F.derivative j (φ z) := by
  classical
  obtain ⟨Cd, _hCd, hdom⟩ := m65SmoothDisk_map_bound φ ψ (fun _ _ => hφ.contDiffAt)
    hψ hφdisk hψdisk hleft hright
  obtain ⟨Cb, _hCb, hbdom⟩ := m65SmoothCircle_map_bound φ ψ hφ.continuous hψ
    hφcircle hψcircle hleft hright
  have hpull {P : LoopPlane → Prop} (hP : ∀ᵐ z ∂volume.restrict loopDiskSet, P z) :
      ∀ᵐ z ∂volume.restrict loopDiskSet, P (φ z) :=
    ae_of_ae_map hφ.continuous.measurable.aemeasurable
      (ae_mono hdom (Measure.ae_smul_measure hP Cd))
  have hbpull {P : LoopPlane → Prop} (hP : ∀ᵐ z ∂m65CircleBoundaryMeasure, P z) :
      ∀ᵐ z ∂m65CircleBoundaryMeasure, P (φ z) :=
    ae_of_ae_map hφ.continuous.measurable.aemeasurable
      (ae_mono hbdom (Measure.ae_smul_measure hP Cb))
  choose u d b hu hd hb htrace using fun j => m65WeakTrace_smooth_change φ ψ hφ hψ
    hφdisk hψdisk hφcircle hψcircle hleft hright (F.weak_trace j)
  let f := e ∘ F.value ∘ φ
  let v (i : Fin 2) (z : LoopPlane) :=
    ∑ k : Fin 2, (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) k •
      F.derivative k (φ z)
  have hu' (j : Fin N) : u j =ᵐ[volume.restrict loopDiskSet] fun z => f z j := by
    filter_upwards [hu j, hpull (m65DiskCoordinateL2_coe F.embeddedValue j),
      hpull F.embeddedValue_ae] with z hz hc hv
    rw [hz, hc, hv]
    rfl
  have hd' (j : Fin N) (i : Fin 2) : d j i =ᵐ[volume.restrict loopDiskSet]
      fun z => v i z j := by
    filter_upwards [hd j i, hpull (m65DiskCoordinateL2_coe (F.derivative 0) j),
      hpull (m65DiskCoordinateL2_coe (F.derivative 1) j)] with z hz h0 h1
    rw [hz]
    simp only [Fin.sum_univ_two, h0, h1, v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hf : MemLp f 2 (volume.restrict loopDiskSet) :=
    MemLp.of_eval_piLp fun j => (Lp.memLp (u j)).ae_eq (hu' j)
  have hv (i : Fin 2) : MemLp (v i) 2 (volume.restrict loopDiskSet) :=
    MemLp.of_eval_piLp fun j => (Lp.memLp (d j i)).ae_eq (hd' j i)
  let U := hf.toLp f
  let V (i : Fin 2) := (hv i).toLp (v i)
  have hU (j : Fin N) : m65DiskCoordinateL2 U j = u j := by
    apply Lp.ext
    filter_upwards [m65DiskCoordinateL2_coe U j, hf.coeFn_toLp, hu' j] with z hz hfu huj
    rw [hz, hfu, huj]
  have hV (j : Fin N) (i : Fin 2) : m65DiskCoordinateL2 (V i) j = d j i := by
    apply Lp.ext
    filter_upwards [m65DiskCoordinateL2_coe (V i) j, (hv i).coeFn_toLp,
      hd' j i] with z hz hvz hdj
    rw [hz, hvz, hdj]
  have hc_mem (z : LoopCircle) : z.val ∈ loopDiskSet := mem_closedBall_zero_iff.mpr z.property.le
  let H : LoopCircle ≃ₜ LoopCircle := {
    toFun := fun z => ⟨φ z, hφcircle z z.property⟩
    invFun := fun z => ⟨ψ z, hψcircle z z.property⟩
    left_inv := fun z => Subtype.ext (hleft z (hc_mem z))
    right_inv := fun z => Subtype.ext (hright z (hc_mem z))
    continuous_toFun := (hφ.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro z
      exact ((hψ z (hc_mem z)).continuousAt.comp continuous_subtype_val.continuousAt) }
  let β := F.parameter.comp ⟨H, H.continuous⟩
  let Γ (j : Fin N) : C(LoopCircle, ℝ) :=
    ⟨fun z => e (γ (F.parameter z)) j,
      (EuclideanSpace.proj j).continuous.comp (he.comp (hγ.comp F.parameter.continuous))⟩
  have hclosed : IsClosed {z : LoopPlane | ‖z‖ = 1} := isClosed_eq continuous_norm continuous_const
  choose W hW using fun j => ContinuousMap.exists_extension'
    hclosed.isClosedEmbedding_subtypeVal (Γ j)
  have hbrep (j : Fin N) : F.boundary j =ᵐ[m65CircleBoundaryMeasure] W j := by
    apply (ae_map_iff Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable
      (measurableSet_eq_fun (Lp.stronglyMeasurable (F.boundary j)).measurable
        (W j).continuous.measurable)).mpr
    filter_upwards [F.boundary_ae j, m65CircleBoundaryPullback_coe (F.boundary j)] with t ht hc
    rw [← hc, ht]
    exact (congrFun (hW j) ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩).symm
  have hnewb (j : Fin N) : m65CircleBoundaryPullback (b j) =ᵐ[
      volume.restrict (Icc (-Real.pi) Real.pi)]
        fun t => e (γ (β ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩)) j := by
    have hh : b j =ᵐ[m65CircleBoundaryMeasure] fun z => W j (φ z) :=
      (hb j).trans (hbpull (hbrep j))
    filter_upwards [m65CircleBoundaryPullback_coe (b j),
      ae_of_ae_map Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable hh]
      with t ht hbz
    rw [ht, hbz]
    exact congrFun (hW j) ⟨φ (Proofs.M58.angularPoint t),
      hφcircle _ (Proofs.M58.norm_angularPoint t)⟩
  let G : M65WeakDisk e γ := {
    value := F.value ∘ φ
    embeddedValue := U
    embeddedValue_ae := hf.coeFn_toLp
    derivative := V
    parameter := β
    weakly_monotone := F.weakly_monotone.comp_homeomorph H
    boundary := b
    boundary_ae := hnewb
    weak_trace := by
      intro j
      rw [hU j]
      simp_rw [hV j]
      exact htrace j }
  exact ⟨G, rfl, fun _ => rfl, fun i => (hv i).coeFn_toLp⟩

end PoincareConjecture
