import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.OpenCylinderModel




theorem exists_of_fiberwise_partial_chart
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] {U : Set M}
    (shape : ChainShape) (ell upper : UnitTwoSphere → ℝ)
    (hell : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ ell)
    (hupper : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper)
    (hwidth : ∀ q : UnitTwoSphere, ell q < upper q)
    (P : OpenPartialHomeomorph M RoundCylinderSpace)
    (hsource : P.source = U)
    (htarget : P.target = match shape with
      | .finite _ _ => {z | ell z.1 < z.2 ∧ z.2 < upper z.1}
      | .forward _ => {z | ell z.1 < z.2}
      | .backward _ => {z | z.2 < upper z.1}
      | .biInfinite => univ)
    (hP : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P P.source)
    (hPi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      P.symm P.target) :
    let phi : UnitTwoSphere → ℝ → ℝ := fun q t => match shape with
      | .finite _ _ => ell q + (upper q - ell q) * t
      | .forward _ => ell q + t / (1 - t)
      | .backward _ => upper q - (1 - t) / t
      | .biInfinite => Real.tan (Real.pi * (t - 1 / 2))
    let psi : UnitTwoSphere → ℝ → ℝ := fun q s => match shape with
      | .finite _ _ => (s - ell q) / (upper q - ell q)
      | .forward _ => (s - ell q) / (1 + (s - ell q))
      | .backward _ => 1 / (1 + (upper q - s))
      | .biInfinite => Real.arctan s / Real.pi + 1 / 2
    let middle : UnitTwoSphere → ℝ := fun q => match shape with
      | .finite _ _ => (ell q + upper q) / 2
      | .forward _ => ell q + 1
      | .backward _ => upper q - 1
      | .biInfinite => 0
    ∃ T : OpenCylinderModel U,
      (∀ z : RoundCylinderSpace,
        T.coordinate z = P.symm (z.1, phi z.1 z.2)) ∧
      (∀ x : M, T.inverse x = ((P x).1, psi (P x).1 (P x).2)) ∧
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ middle ∧
      (∀ q : UnitTwoSphere, (q, middle q) ∈ P.target) ∧
      T.middleSphere = range (fun q : UnitTwoSphere => P.symm (q, middle q)) := by
  let phi : UnitTwoSphere → ℝ → ℝ := fun q t => match shape with
    | .finite _ _ => ell q + (upper q - ell q) * t
    | .forward _ => ell q + t / (1 - t)
    | .backward _ => upper q - (1 - t) / t
    | .biInfinite => Real.tan (Real.pi * (t - 1 / 2))
  let psi : UnitTwoSphere → ℝ → ℝ := fun q s => match shape with
    | .finite _ _ => (s - ell q) / (upper q - ell q)
    | .forward _ => (s - ell q) / (1 + (s - ell q))
    | .backward _ => 1 / (1 + (upper q - s))
    | .biInfinite => Real.arctan s / Real.pi + 1 / 2
  let middle : UnitTwoSphere → ℝ := fun q => match shape with
    | .finite _ _ => (ell q + upper q) / 2
    | .forward _ => ell q + 1
    | .backward _ => upper q - 1
    | .biInfinite => 0
  change ∃ T : OpenCylinderModel U,
    (∀ z : RoundCylinderSpace, T.coordinate z = P.symm (z.1, phi z.1 z.2)) ∧
    (∀ x : M, T.inverse x = ((P x).1, psi (P x).1 (P x).2)) ∧
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ middle ∧
    (∀ q : UnitTwoSphere, (q, middle q) ∈ P.target) ∧
    T.middleSphere = range (fun q : UnitTwoSphere => P.symm (q, middle q))
  have hw (q : UnitTwoSphere) : 0 < upper q - ell q := sub_pos.mpr (hwidth q)
  have hangle {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      Real.pi * (t - 1 / 2) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos, ht.1, ht.2]
  have hphi_mem (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      (q, phi q t) ∈ P.target := by
    rw [htarget]
    cases shape with
    | finite a b =>
      change ell q < ell q + (upper q - ell q) * t ∧
        ell q + (upper q - ell q) * t < upper q
      constructor <;>
        nlinarith [mul_pos (hw q) ht.1, mul_pos (hw q) (sub_pos.mpr ht.2)]
    | forward a =>
      change ell q < ell q + t / (1 - t)
      have hh := div_pos ht.1 (sub_pos.mpr ht.2)
      linarith
    | backward b =>
      change upper q - (1 - t) / t < upper q
      have hh := div_pos (sub_pos.mpr ht.2) ht.1
      linarith
    | biInfinite => exact mem_univ _
  have hpsi_mem (q : UnitTwoSphere) (s : ℝ) (hs : (q, s) ∈ P.target) :
      psi q s ∈ Ioo (0 : ℝ) 1 := by
    rw [htarget] at hs
    cases shape with
    | finite a b =>
      change ell q < s ∧ s < upper q at hs
      change 0 < (s - ell q) / (upper q - ell q) ∧
        (s - ell q) / (upper q - ell q) < 1
      refine ⟨div_pos (sub_pos.mpr hs.1) (hw q), (div_lt_one (hw q)).mpr ?_⟩
      linarith [hs.2]
    | forward a =>
      change ell q < s at hs
      have hv : 0 < s - ell q := sub_pos.mpr hs
      have hd : 0 < 1 + (s - ell q) := by linarith
      change 0 < (s - ell q) / (1 + (s - ell q)) ∧
        (s - ell q) / (1 + (s - ell q)) < 1
      exact ⟨div_pos hv hd, (div_lt_one hd).mpr (by linarith)⟩
    | backward b =>
      change s < upper q at hs
      have hv : 0 < upper q - s := sub_pos.mpr hs
      have hd : 0 < 1 + (upper q - s) := by linarith
      change 0 < 1 / (1 + (upper q - s)) ∧ 1 / (1 + (upper q - s)) < 1
      exact ⟨div_pos zero_lt_one hd, (div_lt_one hd).mpr (by linarith)⟩
    | biInfinite =>
      have ha := Real.arctan_mem_Ioo s
      have hlo : -(1 / 2 : ℝ) < Real.arctan s / Real.pi :=
        (lt_div_iff₀ Real.pi_pos).mpr (by linarith [ha.1])
      have hhi : Real.arctan s / Real.pi < (1 / 2 : ℝ) :=
        (div_lt_iff₀ Real.pi_pos).mpr (by linarith [ha.2])
      change 0 < Real.arctan s / Real.pi + 1 / 2 ∧
        Real.arctan s / Real.pi + 1 / 2 < 1
      exact ⟨by linarith, by linarith⟩
  have hleft_scalar (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      psi q (phi q t) = t := by
    have ht0 : t ≠ 0 := ht.1.ne'
    have ht1 : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
    cases shape with
    | finite a b =>
      dsimp only [phi, psi]
      field_simp [(hw q).ne']; ring
    | forward a =>
      dsimp only [phi, psi]
      field_simp [ht1]; ring
    | backward b =>
      dsimp only [phi, psi]
      field_simp [ht0]; ring
    | biInfinite =>
      dsimp only [phi, psi]
      rw [Real.arctan_tan (hangle ht).1 (hangle ht).2]
      field_simp [Real.pi_pos.ne']; ring
  have hright_scalar (q : UnitTwoSphere) (s : ℝ) (hs : (q, s) ∈ P.target) :
      phi q (psi q s) = s := by
    rw [htarget] at hs
    cases shape with
    | finite a b =>
      dsimp only [phi, psi]
      field_simp [(hw q).ne']; ring
    | forward a =>
      change ell q < s at hs
      have hd : 1 + (s - ell q) ≠ 0 := ne_of_gt (by linarith)
      dsimp only [phi, psi]
      field_simp [hd]; ring
    | backward b =>
      change s < upper q at hs
      have hd : 1 + (upper q - s) ≠ 0 := ne_of_gt (by linarith)
      dsimp only [phi, psi]
      field_simp [hd]; ring
    | biInfinite =>
      dsimp only [phi, psi]
      have heq : Real.pi * (Real.arctan s / Real.pi + 1 / 2 - 1 / 2) =
          Real.arctan s := by
        field_simp [Real.pi_pos.ne']
        ring
      rw [heq, Real.tan_arctan]
  let IC := (𝓡 2).prod 𝓘(ℝ, ℝ)
  let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (0 : ℝ) 1
  let Phi : RoundCylinderSpace → RoundCylinderSpace := fun z => (z.1, phi z.1 z.2)
  let Psi : RoundCylinderSpace → RoundCylinderSpace := fun z => (z.1, psi z.1 z.2)
  have he : ContMDiff IC 𝓘(ℝ, ℝ) ∞ (fun z : RoundCylinderSpace => ell z.1) :=
    hell.comp contMDiff_fst
  have hu : ContMDiff IC 𝓘(ℝ, ℝ) ∞ (fun z : RoundCylinderSpace => upper z.1) :=
    hupper.comp contMDiff_fst
  have hs : ContMDiff IC 𝓘(ℝ, ℝ) ∞ (fun z : RoundCylinderSpace => z.2) :=
    contMDiff_snd
  have hphi_smooth : ContMDiffOn IC 𝓘(ℝ, ℝ) ∞
      (fun z : RoundCylinderSpace => phi z.1 z.2) Omega := by
    cases shape with
    | finite a b => exact (he.add ((hu.sub he).mul hs)).contMDiffOn
    | forward a =>
      exact he.contMDiffOn.add (hs.contMDiffOn.div₀
        (contMDiffOn_const.sub hs.contMDiffOn) (fun z hz => (sub_pos.mpr hz.2.2).ne'))
    | backward b =>
      exact hu.contMDiffOn.sub ((contMDiffOn_const.sub hs.contMDiffOn).div₀
        hs.contMDiffOn (fun z hz => hz.2.1.ne'))
    | biInfinite =>
      have ha : ContMDiff IC 𝓘(ℝ, ℝ) ∞
          (fun z : RoundCylinderSpace => Real.pi * (z.2 - 1 / 2)) :=
        contMDiff_const.mul (hs.sub contMDiff_const)
      intro z hz
      have ht : ContDiffAt ℝ ∞ Real.tan (Real.pi * (z.2 - 1 / 2)) :=
        Real.contDiffAt_tan.mpr (Real.cos_pos_of_mem_Ioo (hangle hz.2)).ne'
      exact ht.comp_contMDiffWithinAt
        (f := fun w : RoundCylinderSpace => Real.pi * (w.2 - 1 / 2))
        (ha z).contMDiffWithinAt
  have hpsi_smooth : ContMDiffOn IC 𝓘(ℝ, ℝ) ∞
      (fun z : RoundCylinderSpace => psi z.1 z.2) P.target := by
    cases shape with
    | finite a b =>
      exact ((hs.sub he).div₀ (hu.sub he) (fun z => (hw z.1).ne')).contMDiffOn
    | forward a =>
      apply (hs.contMDiffOn.sub he.contMDiffOn).div₀
        (contMDiffOn_const.add (hs.contMDiffOn.sub he.contMDiffOn))
      intro z hz
      have hh : ell z.1 < z.2 := by simpa only [htarget, mem_ofPred_eq] using hz
      change 1 + (z.2 - ell z.1) ≠ 0
      linarith
    | backward b =>
      apply contMDiffOn_const.div₀
        (contMDiffOn_const.add (hu.contMDiffOn.sub hs.contMDiffOn))
      intro z hz
      have hh : z.2 < upper z.1 := by simpa only [htarget, mem_ofPred_eq] using hz
      change 1 + (upper z.1 - z.2) ≠ 0
      linarith
    | biInfinite =>
      exact (((Real.contDiff_arctan.comp_contMDiff hs).div₀ contMDiff_const
        (fun _ => Real.pi_pos.ne')).add contMDiff_const).contMDiffOn
  have hPhi : ContMDiffOn IC IC ∞ Phi Omega := contMDiffOn_fst.prodMk hphi_smooth
  have hPsi : ContMDiffOn IC IC ∞ Psi P.target := contMDiffOn_fst.prodMk hpsi_smooth
  have hPhi_mem : MapsTo Phi Omega P.target := fun z hz => hphi_mem z.1 hz.2
  have hPsi_mem : MapsTo Psi P.target Omega :=
    fun z hz => ⟨mem_univ _, hpsi_mem z.1 z.2 hz⟩
  have hPsiPhi : LeftInvOn Psi Phi Omega := by
    intro z hz
    exact Prod.ext rfl (hleft_scalar z.1 hz.2)
  have hPhiPsi : LeftInvOn Phi Psi P.target := by
    intro z hz
    exact Prod.ext rfl (hright_scalar z.1 z.2 hz)
  let C : RoundCylinderSpace → M := fun z => P.symm (Phi z)
  let D : M → RoundCylinderSpace := fun x => Psi (P x)
  have hCmem : MapsTo C Omega U := by
    intro z hz
    rw [← hsource]
    exact P.map_target (hPhi_mem hz)
  have hPmem : MapsTo P U P.target := by
    intro x hx
    apply P.map_source
    rwa [hsource]
  have hDmem : MapsTo D U Omega := fun x hx => hPsi_mem (hPmem hx)
  have hleft : LeftInvOn D C Omega := by
    intro z hz
    change Psi (P (P.symm (Phi z))) = z
    rw [P.right_inv (hPhi_mem hz)]
    exact hPsiPhi hz
  have hright : LeftInvOn C D U := by
    intro x hx
    change P.symm (Phi (Psi (P x))) = x
    rw [hPhiPsi (hPmem hx)]
    apply P.left_inv
    rwa [hsource]
  have hCsmooth : ContMDiffOn IC (𝓡 3) ∞ C Omega := hPi.comp hPhi hPhi_mem
  have hDsmooth : ContMDiffOn (𝓡 3) IC ∞ D U := by
    apply hPsi.comp _ hPmem
    simpa only [hsource] using hP
  let j : UnitTwoSphere × Ioo (0 : ℝ) 1 → RoundCylinderSpace :=
    fun z => (z.1, z.2.1)
  have hj : Continuous j := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hjmem (z : UnitTwoSphere × Ioo (0 : ℝ) 1) : j z ∈ Omega :=
    ⟨mem_univ _, z.2.2⟩
  have hCcont : Continuous (fun z : UnitTwoSphere × Ioo (0 : ℝ) 1 => C (j z)) :=
    hCsmooth.continuousOn.comp_continuous hj hjmem
  have hDcont : Continuous (fun x : U => D x.1) :=
    hDsmooth.continuousOn.comp_continuous continuous_subtype_val (fun x => x.2)
  let H : (UnitTwoSphere × Ioo (0 : ℝ) 1) ≃ₜ U :=
    { toFun := fun z => ⟨C (j z), hCmem (hjmem z)⟩
      invFun := fun x => ((D x.1).1, ⟨(D x.1).2, (hDmem x.2).2⟩)
      left_inv := by
        intro z
        have hh := hleft (hjmem z)
        apply Prod.ext
        · exact congrArg (fun w : RoundCylinderSpace => w.1) hh
        · exact Subtype.ext (congrArg (fun w : RoundCylinderSpace => w.2) hh)
      right_inv := by
        intro x
        apply Subtype.ext
        exact hright x.2
      continuous_toFun := hCcont.subtype_mk (fun z => hCmem (hjmem z))
      continuous_invFun := hDcont.fst.prodMk
        (hDcont.snd.subtype_mk (fun x => (hDmem x.2).2)) }
  let T : OpenCylinderModel U :=
    { homeomorph := H
      coordinate := C
      coordinate_eq := fun _ => rfl
      coordinate_smooth := hCsmooth
      inverse := D
      inverse_mem := fun x hx => hDmem hx
      left_inverse := hleft
      right_inverse := hright
      inverse_smooth := hDsmooth }
  have hmiddle : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ middle := by
    cases shape with
    | finite a b => exact (hell.add hupper).div₀ contMDiff_const (fun _ => by norm_num)
    | forward a => exact hell.add contMDiff_const
    | backward b => exact hupper.sub contMDiff_const
    | biInfinite => exact contMDiff_const
  have hmid (q : UnitTwoSphere) : phi q (1 / 2) = middle q := by
    cases shape with
    | finite a b => norm_num [phi, middle]; ring
    | forward a => norm_num [phi, middle]
    | backward b => norm_num [phi, middle]
    | biInfinite => norm_num [phi, middle]
  refine ⟨T, fun _ => rfl, fun _ => rfl, hmiddle, ?_, ?_⟩
  · intro q
    rw [← hmid q]
    exact hphi_mem q ⟨by norm_num, by norm_num⟩
  · change C '' (univ ×ˢ ({1 / 2} : Set ℝ)) =
      range (fun q : UnitTwoSphere => P.symm (q, middle q))
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht' : t = 1 / 2 := ht
      subst t
      exact ⟨q, by simp only [C, Phi, hmid]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩, by simp only [C, Phi, hmid]⟩

end PoincareConjecture.OpenCylinderModel
