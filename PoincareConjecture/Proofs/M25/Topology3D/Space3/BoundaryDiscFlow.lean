import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalFieldLift
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldChartTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldFlowTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_boundaryDisc_ambient_flow (v : E) (hv : ‖v‖ = 1)
    (f : (ℝ ∙ v)ᗮ → (ℝ ∙ v)ᗮ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {k l : ℝ≥0} (hk : LipschitzWith k f) (hl : ∀ x, ‖f x‖ ≤ l) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      (∀ y, Φ 0 y = y) ∧
      (∀ t y, ‖Φ t y‖ = ‖y‖) ∧
      (∀ t x, Φ t (stereoInvFun hv x : E) =
        (stereoInvFun hv (boundedFlow f hk hl x t) : E)) ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ radialStereoTarget v ∧
        ∀ t y, y ∉ C → Φ t y = y := by
  obtain ⟨χ, hχ, hχc, hχs, hnear, _⟩ := exists_compact_smooth_cutoff
    (K := {(1 : ℝ)}) (U := Ioi 0) isCompact_singleton isOpen_Ioi
    (by intro r hr; simpa only [mem_singleton_iff.mp hr, mem_Ioi] using zero_lt_one)
  have hχone : χ 1 = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnear 1 (mem_singleton 1)).self_of_nhds
  let V := horizontalFieldLift χ f
  let e := radialStereoChart v hv
  have hV : ContDiff ℝ ∞ V := horizontalFieldLift_contDiff χ hχ f hf
  have hVc : HasCompactSupport V := horizontalFieldLift_hasCompactSupport χ hχc f hfc
  have hVs : tsupport V ⊆ e.source := by
    intro p hp
    exact ⟨mem_univ _, hχs ((horizontalFieldLift_tsupport χ f hp).2)⟩
  obtain ⟨kv, lv, hkv, hlv⟩ := compactField_bounds V hV hVc
  obtain ⟨W, hW, hWc, hWs, hpush⟩ := exists_chart_field_extension e
    (radialStereoChart_contDiffOn v hv) (radialStereoChart_symm_contDiffOn v hv) V hV hVc hVs
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds W hW hWc
  have hWt : tsupport W ⊆ e.target := by
    rintro y hy
    obtain ⟨p, hp, rfl⟩ := hWs hy
    exact e.map_source (hVs hp)
  let Φ := fun t => boundedFlowDiffeomorph W hK hL hW hWc t
  refine ⟨Φ, ?_, ?_, ?_, ?_, e '' tsupport V, ?_, ?_, ?_⟩
  · exact (boundedFlow_contDiff W hK hL hW hWc).comp
      (contDiff_snd.prodMk contDiff_fst)
  · intro y
    exact boundedFlow_zero W hK hL y
  · intro t y
    change ‖boundedFlow W hK hL y t‖ = ‖y‖
    by_cases hy : y ∈ e.target
    · let p := e.symm y
      have hps : p ∈ e.source := e.map_target hy
      have hpEq : e p = y := e.right_inv hy
      have htrack := boundedFlow_chart_pushforward e
        (radialStereoChart_contDiffOn v hv) V W hkv hlv hK hL hVs hpush hps t
      rw [← hpEq, htrack]
      have hsnd := horizontalFieldLift_flow_snd χ f hkv hlv p t
      have hpos : 0 < (boundedFlow V hkv hlv p t).2 := by
        rw [hsnd]
        exact hps.2
      change ‖radialStereoMap v hv (boundedFlow V hkv hlv p t)‖ = ‖radialStereoMap v hv p‖
      rw [radialStereoMap_norm v hv _ hpos, radialStereoMap_norm v hv p hps.2, hsnd]
    · rw [boundedFlow_eq_self W hK hL y
        (image_eq_zero_of_notMem_tsupport (fun h => hy (hWt h))) t]
  · intro t x
    change boundedFlow W hK hL (stereoInvFun hv x : E) t =
      (stereoInvFun hv (boundedFlow f hk hl x t) : E)
    have hxs : (x, (1 : ℝ)) ∈ e.source := ⟨mem_univ _, (zero_lt_one : (0 : ℝ) < 1)⟩
    have htrack := boundedFlow_chart_pushforward e
      (radialStereoChart_contDiffOn v hv) V W hkv hlv hK hL hVs hpush hxs t
    change boundedFlow W hK hL (radialStereoMap v hv (x, 1)) t =
      radialStereoMap v hv (boundedFlow V hkv hlv (x, 1) t) at htrack
    rw [horizontalFieldLift_flow_slice χ f hk hl hkv hlv 1 hχone] at htrack
    simpa only [radialStereoMap, one_smul] using htrack
  · exact hVc.isCompact.image_of_continuousOn (e.continuousOn.mono hVs)
  · rintro y ⟨p, hp, rfl⟩
    exact e.map_source (hVs hp)
  · intro t y hy
    exact boundedFlow_eq_self W hK hL y
      (image_eq_zero_of_notMem_tsupport (fun h => hy (hWs h))) t

end PoincareConjecture.M25.Topology3D
