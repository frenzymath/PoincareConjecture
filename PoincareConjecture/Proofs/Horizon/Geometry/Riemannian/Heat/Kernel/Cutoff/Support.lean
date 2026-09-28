import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff.Profile








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma deriv_scale {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {R : ℝ} (_hR : 0 < R) (r : ℝ) :
    deriv (fun s => χ (s / R)) r = deriv χ (r / R) / R := by
  have h := ((hχ.differentiable (by simp) (r / R)).hasDerivAt).comp r
    ((hasDerivAt_id r).div_const R)
  simpa only [one_div, div_eq_mul_inv, one_mul, Function.comp_def, id_eq] using h.deriv

private lemma deriv_deriv_scale {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {R : ℝ} (hR : 0 < R) (r : ℝ) :
    deriv (deriv (fun s => χ (s / R))) r = deriv (deriv χ) (r / R) / R ^ 2 := by
  have he : deriv (fun s => χ (s / R)) = fun s => deriv χ (s / R) / R :=
    funext (deriv_scale hχ hR)
  rw [he, deriv_div_const, deriv_scale (hχ.deriv' (n := ∞)) hR]
  ring



lemma radial_profile_operator_bounds (D : LeviCivitaData g)
    {ρ : M → ℝ} (hρ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    {A B C L R : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hA : ∀ r, deriv χ r ^ 2 ≤ A * χ r)
    (hB : ∀ r, -B ≤ deriv (deriv χ) r) (hC : ∀ r, -C ≤ deriv χ r)
    {x : M} (hgrad : g.inner x (D.gradient ρ x) (D.gradient ρ x) = 1)
    (hlap : D.laplacian ρ x ≤ L) :
    g.inner x (D.gradient (fun y => χ (ρ y / R)) x)
        (D.gradient (fun y => χ (ρ y / R)) x) ≤ A / R ^ 2 * χ (ρ x / R) ∧
      -(B / R ^ 2 + C * L / R) ≤ D.laplacian (fun y => χ (ρ y / R)) x := by
  let F := fun r => χ (r / R)
  have hF : ContDiff ℝ ∞ F := hχ.comp (contDiff_id.div_const R)
  have hd := deriv_scale hχ hR (ρ x)
  have hd2 := deriv_deriv_scale hχ hR (ρ x)
  have hg := D.gradient_comp ((hρ x).mdifferentiableAt (by simp))
    (hF.differentiable (by simp) (ρ x))
  have hl := D.laplacian_comp hρ hF x
  change D.gradient (fun y => χ (ρ y / R)) x = _ at hg
  change D.laplacian (fun y => χ (ρ y / R)) x = _ at hl
  constructor
  · rw [hg]
    simp only [map_smul, smul_apply, smul_eq_mul, hgrad, mul_one]
    rw [show deriv F (ρ x) = deriv χ (ρ x / R) / R from hd]
    have h := div_le_div_of_nonneg_right (hA (ρ x / R)) (sq_nonneg R)
    calc
      _ = deriv χ (ρ x / R) ^ 2 / R ^ 2 := by ring
      _ ≤ A * χ (ρ x / R) / R ^ 2 := h
      _ = _ := by ring
  · rw [hl, hgrad, mul_one]
    change _ ≤ deriv (fun s => χ (s / R)) (ρ x) * D.laplacian ρ x +
      deriv (deriv (fun s => χ (s / R))) (ρ x)
    rw [hd, hd2]
    have hc0 : deriv χ (ρ x / R) / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      hanti.deriv_nonpos hR.le
    have h1 := mul_le_mul_of_nonpos_left hlap hc0
    have h2 := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hC (ρ x / R)) hR.le) hL
    have h3 := div_le_div_of_nonneg_right (hB (ρ x / R)) (sq_nonneg R)
    have hsum := add_le_add (h2.trans h1) h3
    calc
      _ = -C / R * L + -B / R ^ 2 := by ring
      _ ≤ _ := hsum



lemma radial_cutoff_lower_support [T2Space M] (D : LeviCivitaData g)
    {r : M → ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    {A B C L R : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hA : ∀ s, deriv χ s ^ 2 ≤ A * χ s)
    (hB : ∀ s, -B ≤ deriv (deriv χ) s) (hC : ∀ s, -C ≤ deriv χ s)
    {x : M} {U : Set M} {ρ : M → ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hρ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ U)
    (heq : ρ x = r x) (hle : ∀ y ∈ U, r y ≤ ρ y)
    (hgrad : g.inner x (D.gradient ρ x) (D.gradient ρ x) = 1)
    (hlap : D.laplacian ρ x ≤ L) :
    ∃ (V : Set M) (σ : M → ℝ), IsOpen V ∧ x ∈ V ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ V ∧
      σ x = χ (r x / R) ∧ (∀ y ∈ V, σ y ≤ χ (r y / R)) ∧
      g.inner x (D.gradient σ x) (D.gradient σ x) ≤ A / R ^ 2 * χ (r x / R) ∧
      -(B / R ^ 2 + C * L / R) ≤ D.laplacian σ x := by
  obtain ⟨ρ', hρ', hgerm⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hρ hx
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hgerm)
  have hgrad' : D.gradient ρ' x = D.gradient ρ x := by
    unfold gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq hgerm]
  have hbounds := D.radial_profile_operator_bounds hρ' hχ hanti hR hL hA hB hC (x := x)
    (by simpa only [hgrad'] using hgrad)
    (by simpa only [D.laplacian_eq_of_eventuallyEq hgerm] using hlap)
  have hx' : ρ' x = r x := hgerm.self_of_nhds.trans heq
  refine ⟨V, fun y => χ (ρ' y / R), hV, hxV, ?_, by dsimp; rw [hx'], ?_, ?_, hbounds.2⟩
  · exact (hχ.contMDiff.comp (hρ'.div_const R)).contMDiffOn
  · intro y hy
    obtain ⟨hyU, he⟩ := hVU hy
    apply hanti
    rw [he]
    exact div_le_div_of_nonneg_right (hle y hyU) hR.le
  · simpa only [hx'] using hbounds.1

end PoincareConjecture.LeviCivitaData
