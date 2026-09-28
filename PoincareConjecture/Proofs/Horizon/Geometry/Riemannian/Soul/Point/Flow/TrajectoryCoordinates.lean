import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.RadiusReparametrization









noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {M : Type*} [TopologicalSpace M]




theorem exists_trajectory_level_homeomorph
    (Φ : ℝ → M → M) (hΦ : Continuous (fun z : ℝ × M => Φ z.1 z.2))
    (hzero : ∀ x, Φ 0 x = x)
    (hadd : ∀ t s x, Φ (t + s) x = Φ t (Φ s x))
    (p : M) (hfix : ∀ t, Φ t p = p)
    (f : M → ℝ) (hf : Continuous f) (hfp : f p = 0)
    (hpos : ∀ x, x ≠ p → 0 < f x)
    (hmono : ∀ x, x ≠ p → StrictMono (fun t => f (Φ t x)))
    (hsurj : ∀ x, x ≠ p → ∀ s : ℝ, 0 < s → ∃ t : ℝ, f (Φ t x) = s)
    {r : ℝ} (hr : 0 < r) :
    ∃ F : ({x : M // f x = r} × ℝ) ≃ₜ {x : M // x ≠ p},
      ∀ z, (F z).val = Φ z.2 z.1.val := by
  have haway (t : ℝ) (x : M) (hx : x ≠ p) : Φ t x ≠ p := by
    intro heq
    apply hx
    calc
      x = Φ (-t) (Φ t x) := by rw [← hadd, neg_add_cancel, hzero]
      _ = p := by rw [heq, hfix]
  have hlevel (x : {x : M // f x = r}) : x.val ≠ p := by
    intro heq
    have hx := x.property
    rw [heq, hfp] at hx
    linarith
  let N := {x : M // x ≠ p}
  let R := Ioi (0 : ℝ)
  let radius : N × ℝ → R := fun z =>
    ⟨f (Φ z.2 z.1.val), hpos _ (haway _ _ z.1.property)⟩
  have hradius : Continuous radius :=
    (hf.comp (hΦ.comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)))).subtype_mk _
  have hrmono : ∀ x : N, StrictMono (fun t => radius (x, t)) :=
    fun x => hmono x.val x.property
  have hrsurj : ∀ x : N, Function.Surjective (fun t => radius (x, t)) := by
    intro x s
    obtain ⟨t, ht⟩ := hsurj x.val x.property s.val s.property
    exact ⟨t, Subtype.ext ht⟩
  let inverse : N × R → ℝ := fun z =>
    ((hrmono z.1).orderIsoOfSurjective (fun t => radius (z.1, t)) (hrsurj z.1)).symm z.2
  have hinverse : Continuous inverse :=
    continuous_monotoneFamily_inverse radius hradius hrmono hrsurj
  let τ : N → ℝ := fun x => inverse (x, ⟨r, hr⟩)
  have hτ : Continuous τ := hinverse.comp (continuous_id.prodMk continuous_const)
  have hhit (x : N) : f (Φ (τ x) x.val) = r := by
    have h := ((hrmono x).orderIsoOfSurjective (fun t => radius (x, t))
      (hrsurj x)).apply_symm_apply (⟨r, hr⟩ : R)
    exact congrArg Subtype.val h
  let forward : ({x : M // f x = r} × ℝ) → N := fun z =>
    ⟨Φ z.2 z.1.val, haway _ _ (hlevel z.1)⟩
  let backward : N → ({x : M // f x = r} × ℝ) := fun x =>
    (⟨Φ (τ x) x.val, hhit x⟩, -τ x)
  have hτforward (z : {x : M // f x = r} × ℝ) : τ (forward z) = -z.2 := by
    have heq : f (Φ (τ (forward z) + z.2) z.1.val) = f (Φ 0 z.1.val) := by
      rw [hadd, hzero, z.1.property]
      exact hhit (forward z)
    have htime := (hmono z.1.val (hlevel z.1)).injective heq
    linarith
  have hleft : Function.LeftInverse backward forward := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      change Φ (τ (forward z)) (Φ z.2 z.1.val) = z.1.val
      rw [hτforward, ← hadd, neg_add_cancel, hzero]
    · change -τ (forward z) = z.2
      rw [hτforward, neg_neg]
  have hright : Function.RightInverse backward forward := by
    intro x
    apply Subtype.ext
    change Φ (-τ x) (Φ (τ x) x.val) = x.val
    rw [← hadd, neg_add_cancel, hzero]
  have hforward : Continuous forward :=
    (hΦ.comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))).subtype_mk _
  have hbackward : Continuous backward :=
    ((hΦ.comp (hτ.prodMk continuous_subtype_val)).subtype_mk _).prodMk hτ.neg
  exact ⟨{
    toFun := forward
    invFun := backward
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hforward
    continuous_invFun := hbackward
  }, fun _ => rfl⟩

end Poincare.Topology
