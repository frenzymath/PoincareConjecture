import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.MinimumRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.MinimumEnds
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneBoundary.Reflection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Extrema

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereMorseReduction

variable {f : S2 → E3} (M : SphereMorseReduction f)

theorem exists_single_cap_of_local_maximum
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hmax : IsLocalMax (fun q => inner Real (M.v : E3) (g q)) p) :
    ∃ D : SphereSurgeryCoreCap (M.v : E3) g
      ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}),
      P.core = (D.chart '' ball (0 : E2) 1)ᶜ := by
  have hgEmb := M.tree.embedding_of_mem_leaves hg
  have hactual : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun q => inner Real (M.v : E3) (g q)) :=
    (innerSL Real (M.v : E3)).contMDiff.comp hgEmb.contMDiff
  have hc := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hactual.neg hmax.neg
  have hcp : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0 := by
    change mfderiv (𝓡 2) 𝓘(Real, Real)
      (-(fun q => inner Real (M.v : E3) (g q))) p = 0 at hc
    simpa only [mfderiv_neg, neg_eq_zero] using hc
  obtain ⟨q, _, hqmin⟩ := P.isClosed_core.isCompact.exists_isMinOn
    ⟨p, hp⟩ hactual.continuous.continuousOn
  let c := inner Real (M.v : E3) (g p)
  let a := inner Real (M.v : E3) (g q) - 1
  have hbound (y : S2) (hy : y ∈ P.core) : a < inner Real (M.v : E3) (g y) := by
    have hle : inner Real (M.v : E3) (g q) ≤ inner Real (M.v : E3) (g y) := hqmin hy
    dsimp [a]
    linarith
  have hac : a < c := hbound p hp
  obtain ⟨L, hpair, hcore⟩ := P.exists_model_cap_complement hcaps hP
  have hL : L ≠ [] := M.model_cap_list_ne_nil hg P L hcore
  obtain ⟨h, hh, hgerm, hcritical, _, e, σ, hσ, he0, hep, he, hei, het, hform, hhform⟩ :=
    M.exists_auxiliary_height_with_unique_critical_point hg P hP L hpair hcore hp hcp a c
      ⟨hac.le, le_rfl⟩
  let H : S2 → Real := -h
  have hH : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H := hh.neg
  have hnegform : ∀ x ∈ e.source, -inner Real (M.v : E3) (g (e x)) =
      -inner Real (M.v : E3) (g (e 0)) + ∑ i : Fin 2, (-σ i) * x i ^ 2 := by
    intro x hx
    rw [hform x hx, hep]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  have hsign : ∀ i, -σ i = 1 := morse_signs_eq_one_of_isLocalMin
    e he0 (fun i => -σ i) (fun i => by rcases hσ i with h | h <;> simp [h])
    hnegform (by simpa only [hep] using hmax.neg)
  have hnorm : ∀ x ∈ e.source, H (e x) = -c + ‖x‖ ^ 2 := by
    intro x hx
    have haux : H (e x) = -h p + ∑ i : Fin 2, (-σ i) * x i ^ 2 := by
      change -h (e x) = _
      rw [hhform x hx]
      simp only [neg_mul, Finset.sum_neg_distrib]
      ring
    simpa only [hsign, one_mul, ← EuclideanSpace.real_norm_sq_eq,
      (hgerm p hp).eq_of_nhds] using haux
  have hsmall : IsOpen {x : E2 | -c + ‖x‖ ^ 2 < -a} :=
    isOpen_lt (continuous_const.add (continuous_norm.pow 2)) continuous_const
  have hzero : (0 : E2) ∈ {x : E2 | -c + ‖x‖ ^ 2 < -a} := by simpa using neg_lt_neg hac
  obtain ⟨r, hr, hrsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (e.open_source.mem_nhds he0) (hsmall.mem_nhds hzero))
  have hrs : closedBall (0 : E2) r ⊆ e.source := fun x hx => (hrsmall hx).1
  have hrcore : e '' closedBall (0 : E2) r ⊆ interior P.core := by
    rintro y ⟨x, hx, rfl⟩
    exact het (e.map_source (hrs hx))
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr hr.le
  have hrb : -c + r ^ 2 < -a := by
    have ht := (hrsmall (sphere_subset_closedBall hx)).2
    simpa only [mem_ofPred_eq, mem_sphere_zero_iff_norm.mp hx] using ht
  have hunique (y : S2) (hy : H y ∈ Icc (-c) (-a))
      (hyc : mfderiv (𝓡 2) 𝓘(Real, Real) H y = 0) : y = e 0 := by
    have hyband : h y ∈ Icc a c := by
      change -h y ∈ Icc (-c) (-a) at hy
      exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hycrit : mfderiv (𝓡 2) 𝓘(Real, Real) h y = 0 := by
      simpa only [H, mfderiv_neg, neg_eq_zero] using hyc
    have hyp : y ∈ ({p} : Set S2) := hcritical ▸ ⟨hyband, hycrit⟩
    simpa only [mem_singleton_iff, hep] using hyp
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, hbottom, _⟩ :=
    exists_annular_continuation_of_minimum hH e hr hrs hnorm hrb hunique
  have hcorebound (y : S2) (hy : y ∈ P.core) : H y < -a := by
    change -h y < -a
    rw [(hgerm y hy).eq_of_nhds]
    exact neg_lt_neg (hbound y hy)
  have hcover := subset_minimum_disk_annulus_region_of_isPreconnected hH.continuous e hr hrs hnorm
    rfl hrb hδ F hFs hheight hbottom (P.isConnected_core hcaps).isPreconnected
    (fun y hy => (hcorebound y hy).le) (hep ▸ hp)
  let R := heightReflection (mem_sphere_zero_iff_norm.mp M.v.property)
  let G : S2 → E3 := fun y => R (g y)
  let LR : List (SphereSurgeryCoreCap (M.v : E3) G ∅) := L.map (fun D => D.reflected)
  have hLR : LR ≠ [] := fun heq => hL (List.map_eq_nil_iff.mp heq)
  have hpairR : LR.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) := by
    rw [show LR = L.map (fun D => D.reflected) from rfl, List.pairwise_map]
    exact hpair
  have hcoreR : P.core = (⋃ D ∈ LR, D.chart '' ball 0 1)ᶜ := by
    rw [hcore]
    congr 1
    ext y
    simp only [mem_iUnion, LR, List.mem_map]
    constructor
    · rintro ⟨D, hD, hy⟩
      exact ⟨D.reflected, ⟨D, hD, rfl⟩, hy⟩
    · rintro ⟨_, ⟨D, hD, rfl⟩, hy⟩
      exact ⟨D, hD, hy⟩
  have hactualR : EqOn H (fun y => inner Real (M.v : E3) (G y)) P.core := by
    intro y hy
    change -h y = inner Real (M.v : E3) (heightReflection _ (g y))
    rw [inner_heightReflection, (hgerm y hy).eq_of_nhds]
  obtain ⟨DR, hDR, hsingle⟩ := SphereSurgeryCoreCap.exists_unique_cap_of_minimum_component
    LR hLR hpairR hcoreR (P.isConnected_core hcaps).isPreconnected P.isClosed_core.isCompact
    hH.continuous.continuousOn hactualR e hr hrs hnorm rfl hrb hδ hrcore
    F hFs hF hFi hheight hbottom hcover
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hDR
  refine ⟨D, ?_⟩
  rw [hcore]
  congr 1
  ext y
  constructor
  · intro hy
    obtain ⟨A, hA, hyA⟩ := mem_iUnion₂.mp hy
    have hAD := congrArg SphereSurgeryCoreCap.chart
      (hsingle A.reflected (List.mem_map.mpr ⟨A, hA, rfl⟩))
    change A.chart = D.chart at hAD
    rwa [← hAD]
  · intro hy
    exact mem_iUnion_of_mem D (mem_iUnion_of_mem hD hy)

end SphereMorseReduction

end Poincare.Manifold.Schoenflies
