import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.CodimensionZero
import Mathlib.Geometry.Manifold.PartitionOfUnity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]



theorem exists_ambient_isotopy_of_compact_isotopy_within
    {a b : Real} {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (G : Real × E -> E) (hG : ContDiff Real ∞ G)
    (e : OpenPartialHomeomorph (Real × E) (Real × E))
    (he : Icc a b ×ˢ K ⊆ e.source)
    (hei : ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real × E) ∞ e.symm e.target)
    (hagree : ∀ t ∈ Icc a b, ∀ x ∈ K, e (t, x) = (t, G (t, x)))
    (htrace : ∀ t ∈ Icc a b, ∀ x ∈ K, G (t, x) ∈ U) :
    ∃ S : Set E, IsCompact S ∧ S ⊆ U ∧
      ∃ Phi : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun p : Real × E => Phi p.1 p.2) ∧
      (∀ t x, x ∉ S -> Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ x ∈ K, Phi t (G (a, x)) = G (t, x) := by
  obtain ⟨W, hW, hWc, hWon⟩ := exists_velocity_extension_of_compact_isotopy
    hK G hG e he hei hagree
  let T : Set E := G '' (Icc a b ×ˢ K)
  have hT : IsCompact T := (isCompact_Icc.prod hK).image hG.continuous
  have hTU : T ⊆ U := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact htrace t ht x hx
  obtain ⟨S, hS, hTS, hSU⟩ := exists_compact_between hT hU hTU
  obtain ⟨chi, hchi, hchi0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(Real, E) hT.isClosed hTS (n := ⊤)
  let V : Real × E -> E := fun p => chi p.2 • W p
  have hV : ContDiff Real ∞ V := (chi.contMDiff.contDiff.comp contDiff_snd).smul hW
  have hVc : HasCompactSupport V := hWc.smul_left
  have hzero (t : Real) (x : E) (hx : x ∉ S) : V (t, x) = 0 := by
    simp only [V, hchi0 x hx, zero_smul]
  have hVon (t : Real) (ht : t ∈ Icc a b) (x : E) (hx : x ∈ K) :
      V (t, G (t, x)) = fderiv Real G (t, x) (1, 0) := by
    have hp : G (t, x) ∈ T := ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    change chi (G (t, x)) • W (t, G (t, x)) = _
    rw [hchi.self_of_nhdsSet _ hp, one_smul, hWon t ht x hx]
  obtain ⟨Phi, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support V hV hS hzero
  refine ⟨S, hS, hSU, Phi a, hi a, hs a, hfix a, ?_⟩
  intro t ht x hx
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  have hLip (s : Real) : LipschitzWith L (fun y => V (s, y)) := by
    convert! hL.comp (LipschitzWith.prodMk_left s) using 1
    simp
  have hpath (s : Real) : HasDerivAt (fun r => G (r, x))
      (fderiv Real G (s, x) (1, 0)) s := by
    exact (hG.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have heq := ODE_solution_unique hLip
    (HasDerivAt.continuousOn (fun s _ => ho a (G (a, x)) s))
    (fun s _ => (ho a (G (a, x)) s).hasDerivWithinAt)
    (hG.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun s hs => by
      change HasDerivWithinAt (fun r => G (r, x)) (V (s, G (s, x))) (Ici s) s
      rw [hVon s (Ico_subset_Icc_self hs) x hx]
      exact (hpath s).hasDerivWithinAt)
    (hi a (G (a, x)))
  exact heq ht



theorem exists_ambient_isotopy_of_codimZero_isotopy_within
    {a b : Real} {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (G : Real × E -> E) (hG : ContDiff Real ∞ G)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun x => G (t, x)) K)
    (hder : ∀ t ∈ Icc a b, ∀ x ∈ K,
      Function.Bijective (fderiv Real (fun y => G (t, y)) x))
    (htrace : ∀ t ∈ Icc a b, ∀ x ∈ K, G (t, x) ∈ U) :
    ∃ S : Set E, IsCompact S ∧ S ⊆ U ∧
      ∃ Phi : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun p : Real × E => Phi p.1 p.2) ∧
      (∀ t x, x ∉ S -> Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ x ∈ K, Phi t (G (a, x)) = G (t, x) := by
  obtain ⟨e, he, heq, _, hei⟩ :=
    exists_spacetime_neighborhood_of_codimZero_isotopy hK G hG hinj hder
  exact exists_ambient_isotopy_of_compact_isotopy_within hK hU G hG e he hei
    (fun t ht x hx => heq (he ⟨ht, hx⟩)) htrace

end Poincare.Manifold.Schoenflies
