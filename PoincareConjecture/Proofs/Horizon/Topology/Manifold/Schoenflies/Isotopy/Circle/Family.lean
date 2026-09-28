import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Circle.Parametric
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.ParametricExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Family.Velocity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

theorem exists_ambient_isotopy_of_circle_family
    {ι : Type*} [Finite ι] {a b : Real} (hab : a ≤ b)
    (f : ι → Real × sphere (0 : EuclideanSpace Real (Fin 2)) 1 →
      EuclideanSpace Real (Fin 2))
    (hf : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ (f i))
    (hemb : ∀ i t, t ∈ Icc a b → _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun p : sphere (0 : EuclideanSpace Real (Fin 2)) 1 => f i (t, p)))
    (hdisjoint : ∀ t ∈ Icc a b, Function.Injective
      (fun z : ι × sphere (0 : EuclideanSpace Real (Fin 2)) 1 => f z.1 (t, z.2))) :
    ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2)
        (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun z : Real × EuclideanSpace Real (Fin 2) => Phi z.1 z.2) ∧
      (∃ K : Set (EuclideanSpace Real (Fin 2)), IsCompact K ∧
        ∀ t x, x ∉ K → Phi t x = x) ∧
      ∀ i t, t ∈ Icc a b → ∀ p : sphere (0 : EuclideanSpace Real (Fin 2)) 1,
        Phi t (f i (a, p)) = f i (t, p) := by
  classical
  choose G hG heq using fun i => exists_contDiff_extension_sphere_family
    (T := Icc a b) isCompact_Icc (f i) (hf i)
  have hembG (i : ι) : ∀ t ∈ Icc a b, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun p : S1 => G i (t, p)) := by
    intro t ht
    simpa only [funext (heq i t ht)] using hemb i t ht
  have hvelocity (i : ι) : ∃ W : Real × E2 → E2,
      ContDiff Real ∞ W ∧ HasCompactSupport W ∧
      ∀ t ∈ Icc a b, ∀ x ∈ sphere (0 : E2) 1,
        W (t, G i (t, x)) = fderiv Real (G i) (t, x) (1, 0) := by
    obtain ⟨e, he, _, _, hei, _, hagree⟩ :=
      exists_parametric_circle_neighborhood isCompact_Icc (G i) (hG i) (hembG i)
    exact exists_velocity_extension_of_compact_isotopy (isCompact_sphere 0 1)
      (G i) (hG i) e he hei (fun t ht x hx => hagree t ht ⟨x, hx⟩)
  choose V hV hVc hVon using hvelocity
  let T : ι → Set (Real × E2) := fun i =>
    (fun z : Real × E2 => (z.1, G i z)) '' (Icc a b ×ˢ sphere (0 : E2) 1)
  have hT (i : ι) : IsCompact (T i) :=
    (isCompact_Icc.prod (isCompact_sphere 0 1)).image (continuous_fst.prodMk (hG i).continuous)
  have hTdisjoint : Pairwise (fun i j => Disjoint (T i) (T j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨t, x⟩, ⟨ht, hx⟩, hix⟩ ⟨⟨s, y⟩, ⟨hs, hy⟩, hjy⟩
    have he : (t, G i (t, x)) = (s, G j (s, y)) := hix.trans hjy.symm
    have hts : t = s := congrArg Prod.fst he
    subst s
    have hxy : f i (t, ⟨x, hx⟩) = f j (t, ⟨y, hy⟩) := by
      rw [← heq i t ht ⟨x, hx⟩, ← heq j t ht ⟨y, hy⟩]
      exact congrArg Prod.snd he
    exact hij (congrArg Prod.fst ((hdisjoint t ht)
      (a₁ := (i, ⟨x, hx⟩)) (a₂ := (j, ⟨y, hy⟩)) hxy))
  obtain ⟨W, hW, hWc, hWon⟩ :=
    exists_velocity_agreeing_on_finite_disjoint_compacts T hT hTdisjoint V hV hVc
  have hmotion_velocity (i : ι) (t : Real) (ht : t ∈ Icc a b)
      (x : E2) (hx : x ∈ sphere (0 : E2) 1) :
      W (t, G i (t, x)) = fderiv Real (G i) (t, x) (1, 0) := by
    have hmem : (t, G i (t, x)) ∈ T i := ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    exact (hWon i (t, G i (t, x)) hmem).trans (hVon i t ht x hx)
  have hzero : ∀ t x, x ∉ Prod.snd '' tsupport W → W (t, x) = 0 := by
    intro t x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun hp => hx ⟨(t, x), hp, rfl⟩
  obtain ⟨Phi, hi, hs, ho, hfix⟩ := exists_diffeomorph_evolution_of_compact_spatial_support
    W hW (hWc.isCompact.image continuous_snd) hzero
  refine ⟨Phi a, hi a, hs a,
    ⟨Prod.snd '' tsupport W, hWc.isCompact.image continuous_snd, hfix a⟩, ?_⟩
  intro i t ht p
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hWc hW (by simp)
  have hLip (s : Real) : LipschitzWith L (fun y => W (s, y)) := by
    convert! hL.comp (LipschitzWith.prodMk_left s) using 1
    simp
  have hpath (s : Real) : HasDerivAt (fun r => G i (r, p))
      (fderiv Real (G i) (s, p) (1, 0)) s := by
    exact ((hG i).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s (p : E2)))
  have hsolution := ODE_solution_unique hLip
    (HasDerivAt.continuousOn (fun s _ => ho a (G i (a, p)) s))
    (fun s _ => (ho a (G i (a, p)) s).hasDerivWithinAt)
    ((hG i).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun s hst => by
      change HasDerivWithinAt (fun r => G i (r, p)) (W (s, G i (s, p))) (Ici s) s
      rw [hmotion_velocity i s (Ico_subset_Icc_self hst) p p.property]
      exact (hpath s).hasDerivWithinAt)
    (hi a (G i (a, p)))
  simpa only [Function.comp_apply, id_eq, heq i a ⟨le_rfl, hab⟩ p, heq i t ht p]
    using hsolution ht

end Poincare.Manifold.Schoenflies
