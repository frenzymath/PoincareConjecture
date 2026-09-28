import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Height
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.ComponentBand
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.ComponentRegion








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real

namespace SphereMorseReduction

variable {f : S2 → E3} (M : SphereMorseReduction f)



theorem exists_minimum_core_region
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hmin : IsLocalMin (fun q => inner Real (M.v : E3) (g q)) p) :
    ∃ L : List (SphereSurgeryCoreCap (M.v : E3) g
        ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
          {q | mfderiv (𝓡 2) 𝓘(Real, Real)
            (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0})),
      L.Pairwise (fun D E => Disjoint
        (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) ∧
      P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ ∧
      ∃ (h : S2 → Real) (c b : Real),
        ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧
        c = inner Real (M.v : E3) (g p) ∧
        (∀ q ∈ P.core, h =ᶠ[𝓝 q] (fun y => inner Real (M.v : E3) (g y))) ∧
        (∀ q ∈ P.core, h q < b) ∧
        {q | h q ∈ Icc c b ∧ mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0} = {p} ∧
        ∃ (e : OpenPartialHomeomorph E2 S2) (r : Real),
          0 ∈ e.source ∧ e 0 = p ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          e.target ⊆ interior P.core ∧
          (∀ x ∈ e.source, h (e x) = c + ‖x‖ ^ 2) ∧
          0 < r ∧ closedBall (0 : E2) r ⊆ e.source ∧
          e '' closedBall (0 : E2) r ⊆ interior P.core ∧ c + r ^ 2 < b ∧
          ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
            F.source = univ ×ˢ Ioo (c + r ^ 2 - δ) (b + δ) ∧
            ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
            ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
            (∀ q t, t ∈ Ioo (c + r ^ 2 - δ) (b + δ) → h (F (q, t)) = t) ∧
            range (fun q : S1 => F (q, c + r ^ 2)) = e '' sphere (0 : E2) r ∧
            P.core ⊆ e '' closedBall (0 : E2) r ∪ F '' (univ ×ˢ Icc (c + r ^ 2) b) := by
  have hgEmb := M.tree.embedding_of_mem_leaves hg
  have hactual : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun q => inner Real (M.v : E3) (g q)) :=
    (innerSL Real (M.v : E3)).contMDiff.comp hgEmb.contMDiff
  have hc := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hactual hmin
  obtain ⟨q, _, hqmax⟩ := P.isClosed_core.isCompact.exists_isMaxOn
    ⟨p, hp⟩ hactual.continuous.continuousOn
  let c := inner Real (M.v : E3) (g p)
  let b := inner Real (M.v : E3) (g q) + 1
  have hbound (y : S2) (hy : y ∈ P.core) : inner Real (M.v : E3) (g y) < b := by
    have hle : inner Real (M.v : E3) (g y) ≤ inner Real (M.v : E3) (g q) := hqmax hy
    dsimp [b]
    linarith
  have hcb : c < b := hbound p hp
  obtain ⟨L, hpair, hcore⟩ := P.exists_model_cap_complement hcaps hP
  obtain ⟨h, hh, hgerm, hcritical, _, e, σ, hσ, he0, hep, he, hei, het, hform, hhform⟩ :=
    M.exists_auxiliary_height_with_unique_critical_point hg P hP L hpair hcore hp hc c b
      ⟨le_rfl, hcb.le⟩
  have hsign : ∀ i, σ i = 1 := morse_signs_eq_one_of_isLocalMin
    (h := fun y => inner Real (M.v : E3) (g y)) e he0 σ hσ
    (by simpa only [hep] using hform) (by simpa only [hep] using hmin)
  have hnorm : ∀ x ∈ e.source, h (e x) = c + ‖x‖ ^ 2 := by
    intro x hx
    simpa only [hsign, one_mul, ← EuclideanSpace.real_norm_sq_eq,
      (hgerm p hp).eq_of_nhds] using hhform x hx
  have hsmall : IsOpen {x : E2 | c + ‖x‖ ^ 2 < b} :=
    isOpen_lt (continuous_const.add (continuous_norm.pow 2)) continuous_const
  have hzero : (0 : E2) ∈ {x : E2 | c + ‖x‖ ^ 2 < b} := by simpa using hcb
  obtain ⟨r, hr, hrsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (e.open_source.mem_nhds he0) (hsmall.mem_nhds hzero))
  have hrs : closedBall (0 : E2) r ⊆ e.source := fun x hx => (hrsmall hx).1
  have hrcore : e '' closedBall (0 : E2) r ⊆ interior P.core := by
    rintro y ⟨x, hx, rfl⟩
    exact het (e.map_source (hrs hx))
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr hr.le
  have hrb : c + r ^ 2 < b := by
    have h := (hrsmall (sphere_subset_closedBall hx)).2
    simpa only [mem_ofPred_eq, mem_sphere_zero_iff_norm.mp hx] using h
  have hunique (y : S2) (hy : h y ∈ Icc c b)
      (hyc : mfderiv (𝓡 2) 𝓘(Real, Real) h y = 0) : y = e 0 := by
    have hyp : y ∈ ({p} : Set S2) := hcritical ▸ ⟨hy, hyc⟩
    simpa only [mem_singleton_iff, hep] using hyp
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, hbottom, _⟩ :=
    exists_annular_continuation_of_minimum hh e hr hrs hnorm hrb hunique
  have hcorebound (y : S2) (hy : y ∈ P.core) : h y < b := by
    rw [(hgerm y hy).eq_of_nhds]
    exact hbound y hy
  refine ⟨L, hpair, hcore, h, c, b, hh, rfl, hgerm, hcorebound, hcritical,
    e, r, he0, hep, he, hei, het, hnorm, hr, hrs, hrcore, hrb,
    δ, hδ, F, hFs, hF, hFi, hheight, hbottom, ?_⟩
  exact subset_minimum_disk_annulus_region_of_isPreconnected hh.continuous e hr hrs hnorm
    rfl hrb hδ F hFs hheight hbottom (P.isConnected_core hcaps).isPreconnected
    (fun y hy => (hcorebound y hy).le) (hep ▸ hp)

end SphereMorseReduction

end Poincare.Manifold.Schoenflies
