import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

private theorem exists_centered_interval_parameter {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    ∃ r : ℝ → ℝ, FinitePiecewiseAffineOn r I ∧ StrictMonoOn r I ∧ r '' I = J ∧
      r 0 = θ ∧ r (-1) = 0 ∧ r 1 = 1 := by
  let r : ℝ → ℝ := fun t => if t ≤ 0 then θ * (t + 1) else θ + (1 - θ) * t
  let l : ℝ →ᴬ[ℝ] ℝ := θ •
    (ContinuousAffineMap.id ℝ ℝ + ContinuousAffineMap.const ℝ ℝ 1)
  let u : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ θ +
    (1 - θ) • ContinuousAffineMap.id ℝ ℝ
  have hPLleft : FinitePiecewiseAffineOn r (Icc (-1 : ℝ) 0) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (show (-1 : ℝ) < 0 by norm_num)
    apply (show FinitePiecewiseAffineOn l (Icc (-1 : ℝ) 0) from
      ⟨K, hK, hKs, K.affineOnFaces_affine l⟩).congr
    intro x hx
    change θ * (x + 1) = r x
    simp only [r, if_pos hx.2]
  have hPLright : FinitePiecewiseAffineOn r J := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
    apply (show FinitePiecewiseAffineOn u J from
      ⟨K, hK, hKs, K.affineOnFaces_affine u⟩).congr
    intro x hx
    change θ + (1 - θ) * x = r x
    by_cases h : x ≤ 0
    · have hx0 : x = 0 := le_antisymm h hx.1
      simp only [r, hx0, zero_add, mul_one, mul_zero, add_zero, le_refl, if_true]
    · simp only [r, if_neg h]
  have hcover : Icc (-1 : ℝ) 0 ∪ J = I := by
    ext x
    simp only [mem_union, mem_Icc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith
    · intro h
      exact (le_total x 0).elim (fun ht => Or.inl ⟨h.1, ht⟩) (fun ht => Or.inr ⟨ht, h.2⟩)
  have hPL : FinitePiecewiseAffineOn r I := by
    rw [← hcover]
    exact finitePiecewiseAffineOn_union hPLleft hPLright
  have hmono : StrictMonoOn r I := by
    intro x _ y _ hxy
    dsimp only [r]
    split_ifs with hx hy hy
    · nlinarith [mul_pos hθ.1 (sub_pos.mpr hxy)]
    · have hy0 : 0 < y := lt_of_not_ge hy
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hθ.1.le hx,
        mul_pos (sub_pos.mpr hθ.2) hy0]
    · exact False.elim (hx (hxy.le.trans hy))
    · nlinarith [mul_pos (sub_pos.mpr hθ.2) (sub_pos.mpr hxy)]
  have hzero : r 0 = θ := by simp [r]
  have hminus : r (-1) = 0 := by norm_num [r]
  have hplus : r 1 = 1 := by norm_num [r]
  have himage : r '' I = J := by
    have h := hPL.continuousOn.image_Icc_of_monotoneOn
      (show (-1 : ℝ) ≤ 1 by norm_num) hmono.monotoneOn
    simpa only [hminus, hplus] using h
  exact ⟨r, hPL, hmono, himage, hzero, hminus, hplus⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_signed_interval_fiber {N : Set E} {cn cs cp : E}
    (hN : IsFinitePLBallPair ℝ N {cn, cp}) (f : E → ℝ)
    (hf : ContinuousOn f N) (hzero : N ∩ {x | f x = 0} = {cs})
    (hn : f cn < 0) (hp : 0 < f cp) :
    ∃ F : ℝ → E, FinitePiecewiseAffineOn F I ∧ InjOn F I ∧ F '' I = N ∧
      F 0 = cs ∧ F (-1) = cn ∧ F 1 = cp ∧
      (∀ t ∈ I, 0 ≤ f (F t) ↔ 0 ≤ t) ∧
      ∀ t ∈ I, f (F t) ≤ 0 ↔ t ≤ 0 := by
  have hcs : cs ∈ N := (hzero.symm.subset rfl).1
  have hcszero : f cs = 0 := (hzero.symm.subset rfl).2
  have hncp : cn ≠ cp := by intro h; rw [h] at hn; exact (not_lt_of_ge hp.le hn)
  obtain ⟨e, he, he0, he1⟩ := hN.exists_unitInterval_chart_with_endpoints hncp
  obtain ⟨g, hg, heval⟩ := he
  have hgi : InjOn g J := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((heval ⟨x, hx⟩).trans (hxy.trans (heval ⟨y, hy⟩).symm))))
  have hgimage : g '' J = N := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact (heval ⟨t, ht⟩) ▸ (e ⟨t, ht⟩).property
    · intro x hx
      refine ⟨e.symm ⟨x, hx⟩, (e.symm ⟨x, hx⟩).property, ?_⟩
      exact (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
  have hg0 : g 0 = cn := (heval ⟨0, by norm_num⟩).symm.trans he0
  have hg1 : g 1 = cp := (heval ⟨1, by norm_num⟩).symm.trans he1
  let θ : ℝ := e.symm ⟨cs, hcs⟩
  have hθ : θ ∈ J := (e.symm ⟨cs, hcs⟩).property
  have hgθ : g θ = cs :=
    (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨cs, hcs⟩))
  have hθpos : 0 < θ := by
    by_contra h
    have ht : θ = 0 := le_antisymm (le_of_not_gt h) hθ.1
    have heq : cn = cs := hg0.symm.trans (ht ▸ hgθ)
    rw [heq, hcszero] at hn
    exact lt_irrefl _ hn
  have hθone : θ < 1 := by
    by_contra h
    have ht : θ = 1 := le_antisymm hθ.2 (le_of_not_gt h)
    have heq : cp = cs := hg1.symm.trans (ht ▸ hgθ)
    rw [heq, hcszero] at hp
    exact lt_irrefl _ hp
  have hleft : Icc 0 θ ⊆ J := fun _ hx => ⟨hx.1, hx.2.trans hθ.2⟩
  have hright : Icc θ 1 ⊆ J := fun _ hx => ⟨hθ.1.trans hx.1, hx.2⟩
  have hleftBall : IsFinitePLBallPair ℝ (g '' Icc 0 θ) {cn, cs} := by
    simpa only [image_pair, hg0, hgθ] using
      (isFinitePLBallPair_Icc hθpos).image_of_subset hg hleft hgi
  have hrightBall : IsFinitePLBallPair ℝ (g '' Icc θ 1) {cs, cp} := by
    simpa only [image_pair, hgθ, hg1] using
      (isFinitePLBallPair_Icc hθone).image_of_subset hg hright hgi
  have hleftN : g '' Icc 0 θ ⊆ N := (image_mono hleft).trans hgimage.subset
  have hrightN : g '' Icc θ 1 ⊆ N := (image_mono hright).trans hgimage.subset
  have hleftSign : MapsTo f (g '' Icc 0 θ) (Iic 0) := by
    apply hleftBall.mapsTo_nonpos_of_zeros_in_boundary f (hf.mono hleftN)
    · exact fun x hx => Or.inr (hzero.subset ⟨hleftN hx.1, hx.2⟩)
    · exact ⟨cn, hleftBall.1 (Or.inl rfl), hn⟩
  have hrightSign : MapsTo f (g '' Icc θ 1) (Ici 0) := by
    apply hrightBall.mapsTo_nonneg_of_zeros_in_boundary f (hf.mono hrightN)
    · exact fun x hx => Or.inl (hzero.subset ⟨hrightN hx.1, hx.2⟩)
    · exact ⟨cp, hrightBall.1 (Or.inr rfl), hp⟩
  have hgzero (t : ℝ) (ht : t ∈ J) : f (g t) = 0 ↔ t = θ := by
    constructor
    · intro hz
      have heq : g t = cs := hzero.subset ⟨hgimage.subset ⟨t, ht, rfl⟩, hz⟩
      exact hgi ht hθ (heq.trans hgθ.symm)
    · rintro rfl
      rw [hgθ, hcszero]
  have hgpos (t : ℝ) (ht : t ∈ J) : 0 ≤ f (g t) ↔ θ ≤ t := by
    constructor
    · intro h
      by_contra hnle
      have hlt : t < θ := lt_of_not_ge hnle
      have hneg : f (g t) ≤ 0 := hleftSign ⟨t, ⟨ht.1, hlt.le⟩, rfl⟩
      exact hlt.ne ((hgzero t ht).mp (le_antisymm hneg h))
    · intro h
      exact hrightSign ⟨t, ⟨h, ht.2⟩, rfl⟩
  have hgneg (t : ℝ) (ht : t ∈ J) : f (g t) ≤ 0 ↔ t ≤ θ := by
    constructor
    · intro h
      by_contra hnle
      have hlt : θ < t := lt_of_not_ge hnle
      have hpos : 0 ≤ f (g t) := hrightSign ⟨t, ⟨hlt.le, ht.2⟩, rfl⟩
      exact hlt.ne' ((hgzero t ht).mp (le_antisymm h hpos))
    · intro h
      exact hleftSign ⟨t, ⟨ht.1, h⟩, rfl⟩
  obtain ⟨r, hr, hrmono, hrimage, hr0, hrn, hrp⟩ :=
    exists_centered_interval_parameter ⟨hθpos, hθone⟩
  have hrJ : MapsTo r I J := fun t ht => hrimage.subset ⟨t, ht, rfl⟩
  have h0 : (0 : ℝ) ∈ I := by norm_num
  refine ⟨g ∘ r, hg.comp hr hrJ, hgi.comp hrmono.injOn hrJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [image_comp, hrimage, hgimage]
  · exact (congrArg g hr0).trans hgθ
  · exact (congrArg g hrn).trans hg0
  · exact (congrArg g hrp).trans hg1
  · intro t ht
    change 0 ≤ f (g (r t)) ↔ 0 ≤ t
    rw [hgpos (r t) (hrJ ht), ← hr0]
    constructor
    · intro h
      by_contra hnle
      exact not_lt_of_ge h (hrmono ht h0 (lt_of_not_ge hnle))
    · exact fun h => hrmono.monotoneOn h0 ht h
  · intro t ht
    change f (g (r t)) ≤ 0 ↔ t ≤ 0
    rw [hgneg (r t) (hrJ ht), ← hr0]
    constructor
    · intro h
      by_contra hnle
      exact not_lt_of_ge h (hrmono h0 ht (lt_of_not_ge hnle))
    · exact fun h => hrmono.monotoneOn ht h0 h

end PoincareConjecture.M76.HamiltonIndexOne
