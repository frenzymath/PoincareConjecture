import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.TerminalHorizontalProjection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.RadialChart







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem injective_fderiv_preserving_second
    {A : E2 × Real → E2} {q : E2}
    (hA : DifferentiableAt Real A (q, 0))
    (hi : Injective (fderiv Real (fun x => A (x, 0)) q)) :
    Bijective (fderiv Real (fun z : E2 × Real => (A z, z.2)) (q, 0)) := by
  have hd := hA.hasFDerivAt.prodMk (hasFDerivAt_snd (p := (q, (0 : Real))))
  have hsp := hA.hasFDerivAt.comp q (hasFDerivAt_prodMk_left (𝕜 := Real) q (0 : Real))
  simp only [Function.comp_def] at hsp
  have hinj : Injective (fderiv Real (fun z : E2 × Real => (A z, z.2)) (q, 0)) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    rw [hd.fderiv] at hu
    have ht : u.2 = 0 := congrArg Prod.snd hu
    have hx : fderiv Real A (q, 0) u = 0 := congrArg Prod.fst hu
    have hu0 : u = (u.1, 0) := Prod.ext rfl ht
    have hs : fderiv Real (fun x => A (x, 0)) q u.1 = 0 := by
      rw [hsp.fderiv]
      change fderiv Real A (q, 0) (u.1, 0) = 0
      rwa [← hu0]
    have hfirst : u.1 = 0 := hi (hs.trans (map_zero _).symm)
    exact Prod.ext hfirst ht
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

set_option maxHeartbeats 800000 in



theorem exists_horizontal_fiber_chart
    (C : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞)
    (hCs : sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ C.source)
    (h : E3 →L[Real] Real) (c : Real)
    (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hTs : sphere (0 : E2) 1 ⊆ T.source)
    (hTfix : ∀ x ∈ sphere (0 : E2) 1, T x = x)
    (hTh : ∀ x ∈ T.source, h (C (x, 0)) = c + ‖T x‖ - 1) :
    ∃ D : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞,
      sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ D.source ∧
      D.target ⊆ C.target ∧
      (∀ q ∈ sphere (0 : E2) 1, D (q, 0) = C (q, 0)) ∧
      ∀ z ∈ D.source, h (D z) = c + ‖z.1‖ - 1 ∧
        (C.symm (D z)).2 = z.2 := by
  let U := C.source ∩ {z : E2 × Real | z.1 ∈ T.source ∧ T z.1 ≠ 0 ∧
    0 < 1 + h (C z) - c}
  have hU : IsOpen U := by
    have hTopen : IsOpen (T.source ∩ T ⁻¹' ({0}ᶜ : Set E2)) :=
      T.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage T.open_source
        isClosed_singleton.isOpen_compl
    have hCopen : IsOpen (C.source ∩ {z | 0 < 1 + h (C z) - c}) :=
      ((contDiffOn_const.add (h.contDiff.comp_contDiffOn
        C.contMDiffOn_toFun.contDiffOn)).sub contDiffOn_const).continuousOn.isOpen_inter_preimage
          C.open_source isOpen_Ioi
    convert hCopen.inter (hTopen.preimage continuous_fst) using 1
    ext z
    simp only [U, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_compl_iff,
      mem_singleton_iff]
    tauto
  have hKU : sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ U := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨hCs ⟨hq, rfl⟩, hTs hq, ?_, ?_⟩
    · rw [hTfix q hq]
      exact ne_zero_of_mem_unit_sphere ⟨q, hq⟩
    · rw [hTh q (hTs hq), hTfix q hq, mem_sphere_zero_iff_norm.mp hq]
      linarith
  let A : E2 × Real → E2 := fun z => ((1 + h (C z) - c) / ‖T z.1‖) • T z.1
  let B : E2 × Real → E2 × Real := fun z => (A z, z.2)
  have hA : ContDiffOn Real ∞ A U := by
    intro z hz
    have hCz := C.contMDiffOn_toFun.contDiffOn.contDiffAt (C.open_source.mem_nhds hz.1)
    have hTz := T.contMDiffOn_toFun.contDiffOn.contDiffAt (T.open_source.mem_nhds hz.2.1)
    have hTcomp := hTz.comp z contDiffAt_fst
    exact ((((contDiffAt_const.add (h.contDiff.contDiffAt.comp z hCz)).sub
      contDiffAt_const).div ((contDiffAt_norm Real hz.2.2.1).comp z hTcomp)
        (norm_ne_zero_iff.mpr hz.2.2.1)).smul hTcomp).contDiffWithinAt
  have hB : ContDiffOn Real ∞ B U := hA.prodMk contDiffOn_snd
  have hAzero (x : E2) (hx : x ∈ T.source) (hTx : T x ≠ 0) : A (x, 0) = T x := by
    dsimp only [A]
    rw [hTh x hx, show 1 + (c + ‖T x‖ - 1) - c = ‖T x‖ by ring,
      div_self (norm_ne_zero_iff.mpr hTx), one_smul]
  have hBfix (z : E2 × Real) (hz : z ∈ sphere (0 : E2) 1 ×ˢ ({0} : Set Real)) : B z = z := by
    rcases z with ⟨q, t⟩
    have ht : t = 0 := hz.2
    subst t
    exact Prod.ext ((hAzero q (hTs hz.1) (hKU hz).2.2.1).trans (hTfix q hz.1)) rfl
  have hder (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      Bijective (fderiv Real B (q, 0)) := by
    have hqU : (q, (0 : Real)) ∈ U := hKU ⟨hq, rfl⟩
    have hAgerm : (fun x => A (x, 0)) =ᶠ[𝓝 q] T := by
      have hTnonzero : ∀ᶠ x in 𝓝 q, T x ≠ 0 :=
        (T.toOpenPartialHomeomorph.continuousAt (hTs hq))
          (isClosed_singleton.isOpen_compl.mem_nhds hqU.2.2.1)
      filter_upwards [T.open_source.mem_nhds (hTs hq), hTnonzero] with x hx hn
      exact hAzero x hx hn
    have hTlocal := T.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hTs hq)
    have hTi : Injective (fderiv Real (fun x => A (x, 0)) q) := by
      rw [hAgerm.fderiv_eq]
      have hh : Injective (mfderiv (𝓡 2) (𝓡 2) T q) :=
        (hTlocal.mfderivToContinuousLinearEquiv (by simp)).injective
      simpa only [mfderiv_eq_fderiv, TangentSpace] using hh
    exact injective_fderiv_preserving_second
      ((hA.contDiffAt (hU.mem_nhds hqU)).differentiableAt (by simp)) hTi
  have hK : IsCompact (sphere (0 : E2) 1 ×ˢ ({0} : Set Real)) :=
    (isCompact_sphere _ _).prod isCompact_singleton
  obtain ⟨B₀, hB₀, _, hB₀eq⟩ :=
    Poincare.Parabolic.Interior.exists_compact_smooth_extension hK hU hKU hB
  have hlocal (z : E2 × Real) (hz : z ∈ sphere (0 : E2) 1 ×ˢ ({0} : Set Real)) :
      IsLocalDiffeomorphAt 𝓘(Real, E2 × Real) 𝓘(Real, E2 × Real) ∞ B z := by
    have hb : Bijective (fderiv Real B₀ z) := by
      rw [(hB₀eq z hz).fderiv_eq]
      have heq : z = (z.1, 0) := Prod.ext rfl hz.2
      rw [heq]
      exact hder z.1 hz.1
    exact (localDiffeomorphAt_of_smooth_bijective_derivative hB₀ hb).congr_of_eventuallyEq
      (hB₀eq z hz).symm
  obtain ⟨n, hn, _, hnB, hns, hnsi⟩ := Poincare.exists_openPartialHomeomorph_of_injOn_compact
    hK (show InjOn B (sphere (0 : E2) 1 ×ˢ ({0} : Set Real)) by
      intro x hx y hy heq
      rwa [hBfix x hx, hBfix y hy] at heq) hlocal
  let N : PartialDiffeomorph 𝓘(Real, E2 × Real) 𝓘(Real, E2 × Real)
      (E2 × Real) (E2 × Real) ∞ :=
    { n.restrOpen U hU with
      contMDiffOn_toFun := hns.mono inter_subset_left
      contMDiffOn_invFun := hnsi.mono inter_subset_left }
  have hNK : sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ N.source := fun z hz => ⟨hn hz, hKU hz⟩
  have hNB (z : E2 × Real) (hz : z ∈ N.source) : N z = B z := hnB hz.1
  have hNfix (z : E2 × Real) (hz : z ∈ sphere (0 : E2) 1 ×ˢ ({0} : Set Real)) : N z = z :=
    (hNB z (hNK hz)).trans (hBfix z hz)
  have hNt (z : E2 × Real) (hz : z ∈ N.source) : (N z).2 = z.2 := by
    have hh : (N z).2 = (B z).2 := congrArg Prod.snd (hNB z hz)
    exact hh
  let D := N.symm.trans C
  have hDs : D.source = N.target := by
    apply inter_eq_left.mpr
    intro z hz
    exact (N.map_target hz).2.1
  have hDcoord (z : E2 × Real) : D z = C (N.symm z) := rfl
  refine ⟨D, ?_, fun _ hz => hz.1, ?_, ?_⟩
  · intro z hz
    rw [hDs]
    exact hNfix z hz ▸ N.map_source (hNK hz)
  · intro q hq
    rw [hDcoord]
    congr 1
    have heq := N.left_inv (hNK (show (q, (0 : Real)) ∈
      sphere (0 : E2) 1 ×ˢ ({0} : Set Real) from ⟨hq, rfl⟩))
    rwa [hNfix (q, 0) ⟨hq, rfl⟩] at heq
  · intro z hz
    rw [hDs] at hz
    have hi : N.symm z ∈ N.source := N.map_target hz
    have hback : C.symm (D z) = N.symm z := C.left_inv hi.2.1
    have hNinv : N (N.symm z) = z := N.right_inv hz
    have hnorm : ‖(N (N.symm z)).1‖ = 1 + h (C (N.symm z)) - c := by
      rw [hNB (N.symm z) hi]
      change ‖((1 + h (C (N.symm z)) - c) / ‖T (N.symm z).1‖) • T (N.symm z).1‖ = _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hi.2.2.2.2 (norm_pos_iff.mpr hi.2.2.2.1)),
        div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hi.2.2.2.1)]
    rw [hNinv] at hnorm
    refine ⟨?_, ?_⟩
    · rw [hDcoord]
      linarith
    · rw [hback]
      exact (hNt _ hi).symm.trans (congrArg Prod.snd hNinv)

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

set_option maxHeartbeats 800000 in




theorem exists_terminal_model_horizontal_chart
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    ∃ c : Real, (c = data.ends.lowerCut ∨ c = data.ends.upperCut) ∧
      ∃ D : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞,
        sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ D.source ∧
        (∀ q ∈ sphere (0 : E2) 1,
          D (q, 0) = data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q)) ∧
        (∀ y ∈ D.target, sphereProjection
          (data.toTerminalSaddleGeometry.filledModel.symm y) ∈ (data.modelDisk i).target) ∧
        ∀ z ∈ D.source,
          inner Real (M.v : E3) (D z) = c + ‖z.1‖ - 1 ∧
          ‖data.toTerminalSaddleGeometry.filledModel.symm (D z)‖ = 1 + z.2 := by
  obtain ⟨c, hc, T, hTs, _, hTfix, _, hTh⟩ := exists_terminal_model_height_projection data i
  let R := radialDiskChart (data.modelDisk i) (data.modelDisk_smooth i)
    (data.modelDisk_symm_smooth i)
  let C := R.trans data.toTerminalSaddleGeometry.filledModel.toPartialDiffeomorph
  have hCs : sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ C.source := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨data.modelDisk_source i (sphere_subset_closedBall hq), by norm_num⟩, mem_univ _⟩
  have hCzero (x : E2) : C (x, 0) =
      data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x) := by
    change data.toTerminalSaddleGeometry.filledModel
      ((1 + (0 : Real)) • (data.modelDisk i x : E3)) = _
    simp only [add_zero, one_smul]
  obtain ⟨D, hDs, hDt, hDq, hDh⟩ := exists_horizontal_fiber_chart C hCs
    (innerSL Real (M.v : E3)) c T hTs hTfix (fun x hx => by
      rw [hCzero]
      exact hTh x hx)
  refine ⟨c, hc, D, hDs, (fun q hq => (hDq q hq).trans (hCzero q)), ?_, ?_⟩
  · intro y hy
    exact (hDt hy).2.2
  · intro z hz
    refine ⟨(hDh z hz).1, ?_⟩
    have heq := (hDh z hz).2
    change ‖data.toTerminalSaddleGeometry.filledModel.symm (D z)‖ - 1 = z.2 at heq
    linarith

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
