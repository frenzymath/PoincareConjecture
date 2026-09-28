import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaFlux
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabelingConnection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M65Filling

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

set_option maxHeartbeats 1600000 in

theorem exists_differentiable_barrier [T2Space M] [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b)) {J : Set ℝ} (hJ : IsOpen J)
    (hJF : J ⊆ Ioo a b) (C : M65SmoothFilledLoopFamily F J) {q : ℝ} (hq : q ∈ J)
    (hinj : Function.Injective (C.loops q : LoopCircle → M))
    (S : M65MinimalDisk (F.metric q) (F.connection q) (C.loops q)) :
    ∃ (E : ℝ → ℝ) (W : (p : M) → TangentSpace (𝓡 3) p),
      ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
        (fun p => (⟨p, W p⟩ : TangentBundle (𝓡 3) M)) ∧
      (∀ x : ℝ, W (periodicFreeLoop (C.loops q) x) =
        curveVelocity (n := 3) (fun r => periodicFreeLoop (C.loops r) x) q) ∧
      IntegrableOn (m65PlaneRicciTraceDensity (F.connection q) S.disk.map)
        loopDiskSet volume ∧
      E q = fillingArea (F.metric q) (C.loops q) ∧
      (∀ᶠ r in 𝓝 q, fillingArea (F.metric r) (C.loops r) ≤ E r) ∧
      HasDerivAt E
        (-(∫ z in loopDiskSet, m65PlaneRicciTraceDensity (F.connection q) S.disk.map z) +
          ∫ theta in (-Real.pi)..Real.pi,
            (F.metric q).inner (S.disk.map (Proofs.M58.angularPoint theta))
              (W (S.disk.map (Proofs.M58.angularPoint theta)))
              (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
                (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))) q := by
  obtain ⟨d, Phi, V, hd, htime, hPhi, hzero, hV, hode, hboundary⟩ :=
    family_motion F hJ C q hq hinj
  let T := Ioo (q - d) (q + d)
  have hT : IsOpen T := isOpen_Ioo
  have hqT : q ∈ T := by constructor <;> linarith
  have hshift (r : ℝ) (hr : r ∈ T) : r - q ∈ Ioo (-d) d := by
    constructor <;> linarith [hr.1, hr.2]
  have hTF : T ⊆ Ioo a b := by
    intro r hr
    have hh := hJF (htime (r - q) (hshift r hr))
    simpa only [add_sub_cancel] using hh
  let Psi : ℝ × M → M := fun w => Phi (w.2, w.1 - q)
  have hPsi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ Psi (T ×ˢ univ) :=
    hPhi.comp (contMDiff_snd.prodMk (contMDiff_fst.sub contMDiff_const)).contMDiffOn
      (fun w hw => ⟨mem_univ _, hshift w.1 hw.1⟩)
  have hPsi0 (p : M) : Psi (q, p) = p := by
    dsimp only [Psi]
    rw [sub_self, hzero]
  have hPsib (r : ℝ) (hr : r ∈ T) (x : ℝ) :
      Psi (r, periodicFreeLoop (C.loops q) x) = periodicFreeLoop (C.loops r) x := by
    simpa only [Psi, add_sub_cancel] using hboundary (r - q) (hshift r hr) x
  let W := V q
  have hW : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p => (⟨p, W p⟩ : TangentBundle (𝓡 3) M)) :=
    hV.comp (contMDiff_const.prodMk contMDiff_id)
  have hvel (p : M) : curveVelocity (n := 3) (fun r => Psi (r, p)) q = W (Psi (q, p)) := by
    have h0 : (0 : ℝ) ∈ Ioo (-d) d := by constructor <;> linarith
    have hcurve : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 3) (fun r => Phi (p, r)) (q - q) := by
      have hh : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 3) (fun r => Phi (p, r)) 0 :=
        ((hPhi.contMDiffAt (x := (p, 0)) ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨mem_univ p, h0⟩)).comp 0
          ((contMDiffAt_const (c := p)).prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
      simpa only [sub_self] using hh
    have hh := m65CurveVelocity_comp (phi := fun r => r - q) (x := q)
      hcurve ((hasDerivAt_id q).sub_const q)
    have hh' : curveVelocity (n := 3) (fun r => Psi (r, p)) q =
        curveVelocity (n := 3) (fun r => Phi (p, r)) 0 := by
      have he : (curveVelocity (n := 3) (fun r => Phi (p, r)) (q - q) : LoopAmbient) =
          (curveVelocity (n := 3) (fun r => Phi (p, r)) 0 : LoopAmbient) :=
        congrArg (fun r => (curveVelocity (n := 3) (fun s => Phi (p, s)) r : LoopAmbient))
          (sub_self q)
      have hh0 : (curveVelocity (n := 3) (fun r => Psi (r, p)) q : LoopAmbient) =
          (curveVelocity (n := 3) (fun r => Phi (p, r)) (q - q) : LoopAmbient) := by
        simpa only [one_smul, Function.comp_def, Psi] using hh
      exact hh0.trans he
    have ho : curveVelocity (n := 3) (fun r => Phi (p, r)) 0 = W (Phi (p, 0)) := by
      simpa only [add_zero, W] using hode p 0 h0
    have hp0 : Psi (q, p) = Phi (p, 0) :=
      congrArg (fun r => Phi (p, r)) (sub_self q)
    exact hh'.trans (ho.trans (congrArg (fun y => (W y : LoopAmbient)) hp0.symm))
  have hagree (x : ℝ) : W (periodicFreeLoop (C.loops q) x) =
      curveVelocity (n := 3) (fun r => periodicFreeLoop (C.loops r) x) q := by
    have he : (fun r => Psi (r, periodicFreeLoop (C.loops q) x)) =ᶠ[𝓝 q]
        (fun r => periodicFreeLoop (C.loops r) x) := by
      filter_upwards [hT.mem_nhds hqT] with r hr
      exact hPsib r hr x
    have hdv := congrArg (fun L : ℝ →L[ℝ]
        TangentSpace (𝓡 3) (Psi (q, periodicFreeLoop (C.loops q) x)) => L 1)
      (he.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
    change curveVelocity (n := 3) (fun r => Psi (r, periodicFreeLoop (C.loops q) x)) q =
      curveVelocity (n := 3) (fun r => periodicFreeLoop (C.loops r) x) q at hdv
    rw [hvel, hPsi0] at hdv
    exact hdv
  have hmap0 : (fun y => Psi (q, S.disk.map y)) = S.disk.map := funext fun y => hPsi0 _
  obtain ⟨hRI, hder⟩ := disk_energy_firstVariation F hT hTF Psi hPsi S.disk.map
    S.boundary_regular S.interior_smooth hqT W hW hvel
    (fun z hz => by rw [hmap0]; exact S.weakly_conformal z hz)
    (fun z hz => by rw [hmap0]; exact S.harmonic z hz)
  rw [hmap0] at hRI hder
  let E := fun r => ∫ z in loopDiskSet,
    m60EnergyDensity (F.metric r) (fun y => Psi (r, S.disk.map y)) z
  have hE0 : E q = fillingArea (F.metric q) (C.loops q) := by
    dsimp only [E]
    rw [hmap0]
    exact minimal_energy_eq_filling S
  have hbarrier : ∀ᶠ r in 𝓝 q, fillingArea (F.metric r) (C.loops r) ≤ E r := by
    filter_upwards [hT.mem_nhds hqT] with r hr
    have hslice : ContMDiff (𝓡 3) (𝓡 3) 1 (fun p => Psi (r, p)) := by
      apply contMDiffOn_univ.mp
      exact (hPsi.of_le (by simp)).comp
        (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ _ => ⟨hr, mem_univ _⟩)
    exact filling_le_moved_energy S (F.metric r) (C.loops r) (fun p => Psi (r, p))
      hslice (hPsib r hr)
  refine ⟨E, W, hW, hagree, hRI, hE0, hbarrier, ?_⟩
  apply hder.congr_deriv
  congr 1
  apply intervalIntegral.integral_congr
  intro theta _
  let v : LoopAmbient := mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
    (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta)
  exact congrArg (fun p => (F.metric q).inner p (W p) (v : TangentSpace (𝓡 3) p))
    (hPsi0 (S.disk.map (Proofs.M58.angularPoint theta)))

end PoincareConjecture.M65Filling
