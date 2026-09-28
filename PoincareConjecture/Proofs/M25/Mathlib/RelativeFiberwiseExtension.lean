import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseDiffeomorph
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.OpenPartialHomeomorph.Composition












set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u v w

namespace Diffeomorph

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
  {H : Type v} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {K : Type w} [TopologicalSpace K] [ChartedSpace H K]
  [IsManifold I ∞ K]





theorem exists_relative_fiberwise_extension
    (A : Diffeomorph I I K K ∞) (h : K × ℝ → ℝ)
    {a₀ a b b₀ : ℝ} (hleft : a₀ < a) (hab : a < b) (hright : b < b₀)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h
      (univ ×ˢ Ioo a₀ b₀))
    (hhpos : ∀ q : K, ∀ s ∈ Ioo a₀ b₀,
      0 < deriv (fun r : ℝ => h (q, r)) s)
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrange : ∀ s : ℝ, rho s ∈ Ioo a₀ b₀)
    (hagree : EqOn rho id (Icc a b))
    (hrhoderiv : ∀ s : ℝ, deriv rho s ∈ Icc 0 1)
    (hrholeft : ∀ s : ℝ, s ≤ a₀ → rho s = rho a₀)
    (hrhoright : ∀ s : ℝ, b₀ ≤ s → rho s = rho b₀) :
    let F : K × ℝ → ℝ := fun z => h (z.1, rho z.2) + z.2 - rho z.2
    let cminus : K → ℝ := fun q => h (q, rho a₀) - rho a₀
    let cplus : K → ℝ := fun q => h (q, rho b₀) - rho b₀
    let V : Set (K × ℝ) := {z |
      h (A.symm z.1, a) < z.2 ∧ z.2 < h (A.symm z.1, b)}
    ∃ D : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (K × ℝ) (K × ℝ) ∞,
      (∀ z : K × ℝ, D z = (A z.1, F z)) ∧
      (∀ z : K × ℝ,
        (D.symm z).1 = A.symm z.1 ∧ F (D.symm z) = z.2) ∧
      (∀ q : K, ∀ s : ℝ, 0 < deriv (fun r : ℝ => F (q, r)) s) ∧
      (∀ z : K × ℝ, z.2 ∈ Icc a b →
        D z = (A z.1, h z) ∧ D.symm (A z.1, h z) = z) ∧
      (∀ q : K, ∀ s : ℝ, s ≤ a₀ → D (q, s) = (A q, s + cminus q)) ∧
      (∀ q : K, ∀ s : ℝ, b₀ ≤ s → D (q, s) = (A q, s + cplus q)) ∧
      (∀ z : K × ℝ, z.2 ≤ a₀ + cminus (A.symm z.1) →
        D.symm z = (A.symm z.1, z.2 - cminus (A.symm z.1))) ∧
      (∀ z : K × ℝ, b₀ + cplus (A.symm z.1) ≤ z.2 →
        D.symm z = (A.symm z.1, z.2 - cplus (A.symm z.1))) ∧
      D '' (univ ×ˢ Ioo a b) = V ∧
      (∀ z ∈ V, (D.symm z).2 ∈ Ioo a b ∧ h (D.symm z) = z.2) ∧
      let T := D.toHomeomorph.toOpenPartialHomeomorph.restr (univ ×ˢ Ioo a b)
      T.source = univ ×ˢ Ioo a b ∧ T.target = V := by
  classical
  dsimp only
  let F : K × ℝ → ℝ := fun z => h (z.1, rho z.2) + z.2 - rho z.2
  let cminus : K → ℝ := fun q => h (q, rho a₀) - rho a₀
  let cplus : K → ℝ := fun q => h (q, rho b₀) - rho b₀
  let V : Set (K × ℝ) := {z |
    h (A.symm z.1, a) < z.2 ∧ z.2 < h (A.symm z.1, b)}
  have hrhosmooth : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : K × ℝ => rho z.2) :=
    hrho.comp_contMDiff contMDiff_snd
  have hclamp : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : K × ℝ => (z.1, rho z.2)) :=
    contMDiff_fst.prodMk hrhosmooth
  have hhclamp : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : K × ℝ => h (z.1, rho z.2)) :=
    hh.comp_contMDiff hclamp (fun z => ⟨mem_univ _, hrange z.2⟩)
  have hcombine : ContDiff ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => x.1 + x.2.1 - x.2.2) :=
    (contDiff_fst.add (contDiff_fst.comp contDiff_snd)).sub
      (contDiff_snd.comp contDiff_snd)
  have hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F :=
    hcombine.comp_contMDiff
      (hhclamp.prodMk_space (contMDiff_snd.prodMk_space hrhosmooth))
  have hderiv (q : K) (s : ℝ) :
      deriv (fun r : ℝ => F (q, r)) s =
        deriv (fun r : ℝ => h (q, r)) (rho s) * deriv rho s + 1 - deriv rho s := by
    have hhqd : DifferentiableAt ℝ (fun r : ℝ => h (q, r)) (rho s) :=
      differentiableAt_of_deriv_ne_zero (ne_of_gt (hhpos q (rho s) (hrange s)))
    have hrhod := (hrho.differentiable (by simp) s).hasDerivAt
    have hfder := ((hhqd.hasDerivAt.comp s hrhod).fun_add
      (hasDerivAt_id s)).fun_sub hrhod
    simpa only [F, Function.comp_def, id_eq] using hfder.deriv
  have hpos (q : K) (s : ℝ) : 0 < deriv (fun r : ℝ => F (q, r)) s := by
    rw [hderiv]
    have hd := hhpos q (rho s) (hrange s)
    rcases lt_or_eq_of_le (hrhoderiv s).2 with hwlt | hweq
    · have hmul := mul_nonneg hd.le (hrhoderiv s).1
      linarith
    · rw [hweq]
      simpa using hd
  have hFleft (q : K) (s : ℝ) (hs : s ≤ a₀) : F (q, s) = s + cminus q := by
    dsimp only [F, cminus]
    rw [hrholeft s hs]
    ring
  have hFright (q : K) (s : ℝ) (hs : b₀ ≤ s) : F (q, s) = s + cplus q := by
    dsimp only [F, cplus]
    rw [hrhoright s hs]
    ring
  have hsurj (q : K) : Function.Surjective (fun s : ℝ => F (q, s)) := by
    intro y
    let sm : ℝ := min a₀ (y - cminus q) - 1
    let sp : ℝ := max b₀ (y - cplus q) + 1
    have hsm : sm ≤ a₀ := by
      dsimp only [sm]
      linarith [min_le_left a₀ (y - cminus q)]
    have hsp : b₀ ≤ sp := by
      dsimp only [sp]
      linarith [le_max_left b₀ (y - cplus q)]
    have hsmp : sm ≤ sp :=
      hsm.trans ((hleft.trans (hab.trans hright)).le.trans hsp)
    have hlo : F (q, sm) < y := by
      rw [hFleft q sm hsm]
      dsimp only [sm]
      linarith [min_le_right a₀ (y - cminus q)]
    have hhi : y < F (q, sp) := by
      rw [hFright q sp hsp]
      dsimp only [sp]
      linarith [le_max_right b₀ (y - cplus q)]
    have hc : Continuous (fun s : ℝ => F (q, s)) :=
      hF.continuous.comp (continuous_const.prodMk continuous_id)
    obtain ⟨s, _hs, heq⟩ := intermediate_value_Icc hsmp hc.continuousOn ⟨hlo.le, hhi.le⟩
    exact ⟨s, heq⟩
  obtain ⟨D, hD, hDi⟩ := exists_fiberwise_of_deriv_pos A F hF hpos hsurj
  have hmono (q : K) : StrictMono (fun s : ℝ => F (q, s)) :=
    strictMono_of_deriv_pos (hpos q)
  have hFagree (q : K) (s : ℝ) (hs : s ∈ Icc a b) : F (q, s) = h (q, s) := by
    dsimp only [F]
    rw [hagree hs]
    simp
  have hDagree (z : K × ℝ) (hz : z.2 ∈ Icc a b) :
      D z = (A z.1, h z) := by
    rw [hD z]
    exact Prod.ext rfl (hFagree z.1 z.2 hz)
  have hDleft (q : K) (s : ℝ) (hs : s ≤ a₀) :
      D (q, s) = (A q, s + cminus q) := by
    rw [hD (q, s), hFleft q s hs]
  have hDright (q : K) (s : ℝ) (hs : b₀ ≤ s) :
      D (q, s) = (A q, s + cplus q) := by
    rw [hD (q, s), hFright q s hs]
  have hDileft (z : K × ℝ) (hz : z.2 ≤ a₀ + cminus (A.symm z.1)) :
      D.symm z = (A.symm z.1, z.2 - cminus (A.symm z.1)) := by
    apply D.injective
    change D (D.symm z) = D (A.symm z.1, z.2 - cminus (A.symm z.1))
    rw [D.apply_symm_apply, hDleft (A.symm z.1)
      (z.2 - cminus (A.symm z.1)) (by linarith)]
    simp
  have hDiright (z : K × ℝ) (hz : b₀ + cplus (A.symm z.1) ≤ z.2) :
      D.symm z = (A.symm z.1, z.2 - cplus (A.symm z.1)) := by
    apply D.injective
    change D (D.symm z) = D (A.symm z.1, z.2 - cplus (A.symm z.1))
    rw [D.apply_symm_apply, hDright (A.symm z.1)
      (z.2 - cplus (A.symm z.1)) (by linarith)]
    simp
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hinverse (z : K × ℝ) (hz : z ∈ V) :
      (D.symm z).2 ∈ Ioo a b ∧ h (D.symm z) = z.2 := by
    change h (A.symm z.1, a) < z.2 ∧ z.2 < h (A.symm z.1, b) at hz
    have hbase := (hDi z).1
    have hheight : F (A.symm z.1, (D.symm z).2) = z.2 := by
      rw [← hbase]
      exact (hDi z).2
    have hlo : a < (D.symm z).2 := by
      by_contra hnot
      have hle := (hmono (A.symm z.1)).monotone (le_of_not_gt hnot)
      rw [hheight, hFagree (A.symm z.1) a ha] at hle
      exact (not_le_of_gt hz.1) hle
    have hhi : (D.symm z).2 < b := by
      by_contra hnot
      have hle := (hmono (A.symm z.1)).monotone (le_of_not_gt hnot)
      rw [hheight, hFagree (A.symm z.1) b hb] at hle
      exact (not_le_of_gt hz.2) hle
    refine ⟨⟨hlo, hhi⟩, ?_⟩
    exact (hFagree (D.symm z).1 (D.symm z).2 ⟨hlo.le, hhi.le⟩).symm.trans (hDi z).2
  have himage : D '' (univ ×ˢ Ioo a b) = V := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change h (A.symm (D x).1, a) < (D x).2 ∧
        (D x).2 < h (A.symm (D x).1, b)
      rw [hD x]
      simp only [A.symm_apply_apply]
      rw [← hFagree x.1 a ha, ← hFagree x.1 b hb]
      exact ⟨hmono x.1 hx.2.1, hmono x.1 hx.2.2⟩
    · intro hz
      exact ⟨D.symm z, ⟨mem_univ _, (hinverse z hz).1⟩, D.apply_symm_apply z⟩
  let T := D.toHomeomorph.toOpenPartialHomeomorph.restr (univ ×ˢ Ioo a b)
  have hTsource : T.source = univ ×ˢ Ioo a b := by
    dsimp only [T]
    rw [D.toHomeomorph.toOpenPartialHomeomorph.restr_source' _
      (isOpen_univ.prod isOpen_Ioo)]
    simp
  have hTtarget : T.target = V := by
    calc
      T.target = T '' T.source := T.image_source_eq_target.symm
      _ = D '' (univ ×ˢ Ioo a b) := by rw [hTsource]; rfl
      _ = V := himage
  refine ⟨D, hD, hDi, hpos, ?_, hDleft, hDright, hDileft, hDiright,
    himage, hinverse, hTsource, hTtarget⟩
  intro z hz
  refine ⟨hDagree z hz, ?_⟩
  rw [← hDagree z hz, D.symm_apply_apply]

end Diffeomorph
