import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.MinimumRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.MinimumEnds
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneBoundary.Maximum
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Extrema



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 -> E3} (M : SphereMorseReduction f)



theorem exists_single_cap_of_local_minimum
    {g : S2 -> E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hmin : IsLocalMin (fun q => inner Real (M.v : E3) (g q)) p) :
    ∃ D : SphereSurgeryCoreCap (M.v : E3) g
        ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
          {q | mfderiv (𝓡 2) 𝓘(Real, Real)
            (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}),
      P.core = (D.chart '' ball (0 : E2) 1)ᶜ := by
  obtain ⟨L, hpair, hcore, h, c, b, hh, _, hgerm, _, _,
      e, r, _, _, _, _, _, hform, hr, hrs, hdisk, hab,
      δ, hδ, F, hFs, hF, hFi, hheight, hbottom, hcover⟩ :=
    M.exists_minimum_core_region hg P hP hcaps hp hmin
  obtain ⟨D, hD, hsingle⟩ := SphereSurgeryCoreCap.exists_unique_cap_of_minimum_component
    L (M.model_cap_list_ne_nil hg P L hcore) hpair hcore
    (P.isConnected_core hcaps).isPreconnected P.isClosed_core.isCompact hh.continuous.continuousOn
    (fun q hq => (hgerm q hq).eq_of_nhds) e hr hrs hform rfl hab hδ hdisk
    F hFs hF hFi hheight hbottom hcover
  refine ⟨D, hcore.trans ?_⟩
  congr 1
  ext q
  simp only [mem_iUnion]
  constructor
  · rintro ⟨A, hA, hq⟩
    rwa [hsingle A hA] at hq
  · exact fun hq => ⟨D, hD, hq⟩



theorem exists_ambient_filling_of_minimum_core
    {g : S2 -> E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hmin : IsLocalMin (fun q => inner Real (M.v : E3) (g q)) p) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = range g := by
  obtain ⟨D, hcore⟩ := M.exists_single_cap_of_local_minimum hg P hP hcaps hp hmin
  exact M.exists_filling_of_one_cap hg P hP D hcore

end Poincare.Manifold.Schoenflies.SphereMorseReduction
