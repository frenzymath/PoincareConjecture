import PoincareConjecture.Proofs.M63.Mathlib.ManifoldFlatGluing
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic










set_option autoImplicit false

open Filter Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ell : ℝ} {p : ℝ → M} {phi : ℝ → ℝ}



theorem contMDiffAt_comp_of_flat_cells_vertex (hell : 0 < ell)
    (alpha : ℤ → ℝ → M)
    (halpha : ∀ (j : ℤ) (s : ℝ), s ∈ Icc 0 ell → ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (alpha j) s)
    (hagreement : ∀ (j : ℤ) (s : ℝ), s ∈ Icc 0 ell → p ((j : ℝ) * ell + s) = alpha j s)
    (hphi : ContDiff ℝ ∞ phi) (hmono : StrictMono phi)
    (hfix : ∀ j : ℤ, phi ((j : ℝ) * ell) = (j : ℝ) * ell)
    (hflat : ∀ (j : ℤ) (i : ℕ), 0 < i → iteratedDeriv i phi ((j : ℝ) * ell) = 0)
    (j : ℤ) : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (p ∘ phi) ((j : ℝ) * ell) := by
  let c : ℝ := (j : ℝ) * ell
  let left : ℝ := ((j - 1 : ℤ) : ℝ) * ell
  let f : ℝ → M := fun u => alpha (j - 1) (u - left)
  let g : ℝ → M := fun u => alpha j (u - c)
  have hleft : c - left = ell := by dsimp [c, left]; push_cast; ring
  have hphi_c : phi c = c := hfix j
  have hf : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ f c :=
    (halpha (j - 1) ell ⟨hell.le, le_rfl⟩).comp_of_eq
      (contDiffAt_id.sub contDiffAt_const).contMDiffAt hleft
  have hg : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ g c :=
    (halpha j 0 ⟨le_rfl, hell.le⟩).comp_of_eq
      (contDiffAt_id.sub contDiffAt_const).contMDiffAt (sub_self c)
  have hmatch : f c = g c := by
    have hl := hagreement (j - 1) ell ⟨hell.le, le_rfl⟩
    have hr := hagreement j 0 ⟨le_rfl, hell.le⟩
    change p (left + ell) = alpha (j - 1) ell at hl
    change p (c + 0) = alpha j 0 at hr
    rw [show left + ell = c by linarith] at hl
    simpa only [f, g, hleft, sub_self] using hl.symm.trans (by simpa only [add_zero] using hr)
  have hsmooth := contMDiffAt_piecewise_comp_of_flat I hf hg hmatch hphi.contDiffAt
    hphi_c (hflat j)
  apply hsmooth.congr_of_eventuallyEq
  have hnbhd : Ioo left (c + ell) ∈ 𝓝 (phi c) := by
    rw [hphi_c]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hnear : ∀ᶠ y in 𝓝 c, phi y ∈ Ioo left (c + ell) := hphi.continuous.continuousAt hnbhd
  filter_upwards [hnear] with y hy
  change p (phi y) = (Iic c).piecewise (f ∘ phi) (g ∘ phi) y
  by_cases hle : y ≤ c
  · simp only [piecewise, mem_Iic, if_pos hle, Function.comp_apply, f]
    have hupper : phi y ≤ c := (hmono.monotone hle).trans_eq hphi_c
    have hs : phi y - left ∈ Icc 0 ell := by
      constructor <;> linarith [hy.1]
    have ha := hagreement (j - 1) (phi y - left) hs
    change p (left + (phi y - left)) = _ at ha
    simpa only [← add_sub_assoc, add_sub_cancel_left] using ha
  · simp only [piecewise, mem_Iic, if_neg hle, Function.comp_apply, g]
    have hlower : c < phi y := hphi_c.symm.trans_lt (hmono (lt_of_not_ge hle))
    have hs : phi y - c ∈ Icc 0 ell := by
      constructor <;> linarith [hy.2]
    have ha := hagreement j (phi y - c) hs
    change p (c + (phi y - c)) = _ at ha
    simpa only [← add_sub_assoc, add_sub_cancel_left] using ha




theorem contMDiff_comp_of_flat_cells (hell : 0 < ell)
    (alpha : ℤ → ℝ → M)
    (halpha : ∀ (j : ℤ) (s : ℝ), s ∈ Icc 0 ell → ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (alpha j) s)
    (hagreement : ∀ (j : ℤ) (s : ℝ), s ∈ Icc 0 ell → p ((j : ℝ) * ell + s) = alpha j s)
    (hphi : ContDiff ℝ ∞ phi) (hmono : StrictMono phi)
    (hfix : ∀ j : ℤ, phi ((j : ℝ) * ell) = (j : ℝ) * ell)
    (hflat : ∀ (j : ℤ) (i : ℕ), 0 < i → iteratedDeriv i phi ((j : ℝ) * ell) = 0) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (p ∘ phi) := by
  intro x
  let j : ℤ := ⌊x / ell⌋
  have hlow : (j : ℝ) * ell ≤ x := (le_div_iff₀ hell).mp (Int.floor_le (x / ell))
  have hupp : x < (j : ℝ) * ell + ell := by
    have h := (div_lt_iff₀ hell).mp (Int.lt_floor_add_one (x / ell))
    change x < ((j : ℝ) + 1) * ell at h
    nlinarith
  rcases eq_or_lt_of_le hlow with heq | hlt
  · rw [← heq]
    exact contMDiffAt_comp_of_flat_cells_vertex I hell alpha halpha hagreement
      hphi hmono hfix hflat j
  · have hstart : (j : ℝ) * ell < phi x := (hfix j).symm.trans_lt (hmono hlt)
    have hend : (j : ℝ) * ell + ell = ((j + 1 : ℤ) : ℝ) * ell := by push_cast; ring
    have hfinish : phi x < (j : ℝ) * ell + ell := by
      have h := hmono hupp
      rw [hend, hfix (j + 1), ← hend] at h
      exact h
    have hs : phi x - (j : ℝ) * ell ∈ Icc 0 ell := by constructor <;> linarith
    have hsmooth := (halpha j _ hs).comp x
      (hphi.contDiffAt.sub contDiffAt_const).contMDiffAt
    apply hsmooth.congr_of_eventuallyEq
    have hnear : ∀ᶠ y in 𝓝 x, phi y ∈ Ioo ((j : ℝ) * ell) ((j : ℝ) * ell + ell) :=
      hphi.continuous.continuousAt (Ioo_mem_nhds hstart hfinish)
    filter_upwards [hnear] with y hy
    change p (phi y) = alpha j (phi y - (j : ℝ) * ell)
    have hys : phi y - (j : ℝ) * ell ∈ Icc 0 ell := by constructor <;> linarith [hy.1, hy.2]
    simpa only [← add_sub_assoc, add_sub_cancel_left] using
      hagreement j (phi y - (j : ℝ) * ell) hys
