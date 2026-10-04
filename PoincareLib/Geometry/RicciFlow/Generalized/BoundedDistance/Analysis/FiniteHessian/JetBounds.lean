import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.Riemannian.Coordinates.Transition.JetBounds

/-!
# Finite jets at a family of points

These pointwise estimates support the finite Hessian induction for neck maps
in Morgan-Tian Proposition 9.79, pp. 233-234, and Proposition 10.7 and
Claim 10.8, pp. 253-254. Unlike a bound on every jet of a map, a bound on its derivative
does not constrain its value. See M28 derivation 10, section 3.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.Proofs.M28.FiniteHessian

variable {ι E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A family has uniformly bounded jets through `n` at its chosen points.
The bound may vary with the derivative order, but not with the family index.
This is the finite pointwise input in M28 derivation 10, section 3. -/
def HasUniformJetBoundsAt (n : ℕ) (f : ι → E → F) (x : ι → E) : Prop :=
  ∀ m : ℕ, m ≤ n → ∃ C : ℝ, ∀ i,
    ‖iteratedFDeriv ℝ m (f i) (x i)‖ ≤ C

/-- Fewer tested orders preserve a finite jet bound, as used in the finite
Hessian induction of M28 derivation 10, section 3. -/
theorem HasUniformJetBoundsAt.mono_order {m n : ℕ} {f : ι → E → F} {x : ι → E}
    (h : HasUniformJetBoundsAt n f x) (hmn : m ≤ n) :
    HasUniformJetBoundsAt m f x :=
  fun j hj => h j (hj.trans hmn)

/-- A finite list of uniform jet bounds has one nonnegative common bound.
Source: the finite-jet transfer in M28 derivation 10, section 3. -/
theorem HasUniformJetBoundsAt.bound_all {n : ℕ} {f : ι → E → F} {x : ι → E}
    (h : HasUniformJetBoundsAt n f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, m ≤ n → ∀ i,
      ‖iteratedFDeriv ℝ m (f i) (x i)‖ ≤ C := by
  classical
  choose c hc using fun j : Finset.range (n + 1) =>
    h j.1 (Nat.le_of_lt_succ (Finset.mem_range.1 j.2))
  let C : ℝ := ∑ j : Finset.range (n + 1), max (c j) 0
  refine ⟨C, Finset.sum_nonneg (fun j _ => le_max_right _ _), ?_⟩
  intro m hm i
  let j : Finset.range (n + 1) := ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm)⟩
  exact (hc j i).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun k _ => le_max_right _ _) (Finset.mem_univ j)))

/-- Equality of actual smooth germs preserves all tested jets. No off-domain
value is used in the coordinate transfer of M28 derivation 10, section 3. -/
theorem HasUniformJetBoundsAt.congr_germ {n : ℕ} {f g : ι → E → F} {x : ι → E}
    (h : HasUniformJetBoundsAt n f x) (heq : ∀ i, f i =ᶠ[𝓝 (x i)] g i) :
    HasUniformJetBoundsAt n g x := by
  intro m hm
  obtain ⟨C, hC⟩ := h m hm
  refine ⟨C, fun i => ?_⟩
  rw [← ((heq i).iteratedFDeriv ℝ m).eq_of_nhds]
  exact hC i

/-- One derivative raises a finite jet bound by one when the zeroth value is
bounded. Applied to `Df`, this never bounds `f` itself; see derivation 10. -/
theorem HasUniformJetBoundsAt.succ_of_fderiv {n : ℕ} {f : ι → E → F} {x : ι → E}
    (hzero : ∃ C : ℝ, ∀ i, ‖f i (x i)‖ ≤ C)
    (h : HasUniformJetBoundsAt n (fun i => fderiv ℝ (f i)) x) :
    HasUniformJetBoundsAt (n + 1) f x := by
  intro m hm
  cases m with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hzero
  | succ m =>
      obtain ⟨C, hC⟩ := h m (by omega)
      exact ⟨C, fun i => by simpa only [norm_iteratedFDeriv_fderiv] using hC i⟩

/-- A fixed continuous linear operation preserves finite pointwise jet bounds.
Source: M28 derivation 10, section 3, coordinate tensor reconstruction. -/
theorem HasUniformJetBoundsAt.clm {n : ℕ} {f : ι → E → F} {x : ι → E}
    (h : HasUniformJetBoundsAt n f x)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i)) (L : F →L[ℝ] G) :
    HasUniformJetBoundsAt n (fun i y => L (f i y)) x := by
  intro m hm
  obtain ⟨C, hC⟩ := h m hm
  refine ⟨‖L‖ * C, fun i => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left (hf i)
    (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)).trans
      (mul_le_mul_of_nonneg_left (hC i) (norm_nonneg L))

/-- Subtracting smooth germs preserves finite pointwise jet bounds.
Source: the Hessian equation in M28 derivation 10, section 3. -/
theorem HasUniformJetBoundsAt.sub {n : ℕ} {f g : ι → E → F} {x : ι → E}
    (hf : HasUniformJetBoundsAt n f x) (hg : HasUniformJetBoundsAt n g x)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) :
    HasUniformJetBoundsAt n (fun i y => f i y - g i y) x := by
  intro m hm
  obtain ⟨C, hC⟩ := hf m hm
  obtain ⟨D, hD⟩ := hg m hm
  refine ⟨C + D, fun i => ?_⟩
  change ‖iteratedFDeriv ℝ m (f i - g i) (x i)‖ ≤ C + D
  rw [iteratedFDeriv_sub_apply
    ((hcf i).of_le (by exact_mod_cast le_top))
    ((hcg i).of_le (by exact_mod_cast le_top))]
  exact (norm_sub_le _ _).trans (add_le_add (hC i) (hD i))

/-- The local bilinear Leibniz estimate only requires smooth germs. This is
the pointwise product estimate used in M28 derivation 10, section 3. -/
theorem norm_iteratedFDeriv_bilinear_le_at
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (m - j) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn
    (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn
    (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h

/-- A fixed bilinear operation preserves finite pointwise jet bounds.
Source: the finite Hessian induction in M28 derivation 10, section 3. -/
theorem HasUniformJetBoundsAt.bilinear {n : ℕ} {f : ι → E → F} {g : ι → E → G}
    {x : ι → E} (hf : HasUniformJetBoundsAt n f x) (hg : HasUniformJetBoundsAt n g x)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) (B : F →L[ℝ] G →L[ℝ] H) :
    HasUniformJetBoundsAt n (fun i y => B (f i y) (g i y)) x := by
  obtain ⟨C, hC0, hC⟩ := hf.bound_all
  obtain ⟨D, hD0, hD⟩ := hg.bound_all
  intro m hm
  refine ⟨‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * C * D,
    fun i => ?_⟩
  refine (norm_iteratedFDeriv_bilinear_le_at B (hcf i) (hcg i) m).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  gcongr
  · exact hC j (hjm.trans hm) i
  · exact hD (m - j) ((Nat.sub_le _ _).trans hm) i

/-- Composition of operator-valued germs preserves finite pointwise jets.
Source: the connection terms in M28 derivation 10, section 3. -/
theorem HasUniformJetBoundsAt.clm_comp {n : ℕ}
    {f : ι → E → G →L[ℝ] H} {g : ι → E → F →L[ℝ] G} {x : ι → E}
    (hf : HasUniformJetBoundsAt n f x) (hg : HasUniformJetBoundsAt n g x)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) :
    HasUniformJetBoundsAt n (fun i y => (f i y).comp (g i y)) x :=
  hf.bilinear hg hcf hcg (ContinuousLinearMap.compL ℝ F G H)

/-- Composition needs positive jets of the inner map, not its value. Bounds
on `Df` supply these jets in M28 derivation 10, section 3. -/
theorem HasUniformJetBoundsAt.comp_of_fderiv {n : ℕ}
    {f : ι → E → F} {g : ι → F → G} {x : ι → E}
    (hf : HasUniformJetBoundsAt n (fun i => fderiv ℝ (f i)) x)
    (hg : HasUniformJetBoundsAt n g (fun i => f i (x i)))
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (f i (x i))) :
    HasUniformJetBoundsAt n (fun i => g i ∘ f i) x := by
  obtain ⟨C, _, hC⟩ := hf.bound_all
  obtain ⟨D, _, hD⟩ := hg.bound_all
  intro m hm
  refine ⟨Nat.factorial m * D * (max C 1) ^ m, fun i => ?_⟩
  apply CoordinateTransition.norm_iteratedFDeriv_comp_le_of_contDiffAt
    ((hcg i).of_le (by exact_mod_cast le_top))
    ((hcf i).of_le (by exact_mod_cast le_top))
  · intro j hj
    exact hD j (hj.trans hm) i
  · intro j hjpos hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [← norm_iteratedFDeriv_fderiv]
    exact (hC k (by omega) i).trans
      ((le_max_left C 1).trans
        (le_self_pow₀ (le_max_right C 1) (by omega)))

end PoincareMT.Proofs.M28.FiniteHessian
