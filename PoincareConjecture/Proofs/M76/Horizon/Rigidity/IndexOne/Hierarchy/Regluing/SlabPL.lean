import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.PairedHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.PeriodPL

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus.StandardToSourceSlab

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem polyhedralPL_comp_of_slab_restriction
    {V α β : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    {phi : C(H, H)} {M : PairedMeridianHierarchy e d phi} {uv : ℝ × ℝ}
    {m : ExactSlabMeridian M uv} (S : StandardToSourceSlab m)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (f : C(R, R))
    (hrestriction : ∀ x : sourceSlab (ContinuousMap.id H) uv.1 uv.2,
      (f ⟨x, sourceSlab_subset _ _ _ x.property⟩ : X) = S.map x)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite) (q : V → R)
    (hq : PolyhedralPLInCharts d (fun z => (q z : X)) K.space)
    (hmap : MapsTo (fun z => (q z : X)) K.space
      (sourceSlab (ContinuousMap.id H) uv.1 uv.2)) :
    PolyhedralPLInCharts e (fun z => (f (q z) : X)) K.space := by
  classical
  by_cases hne : K.space.Nonempty
  · obtain ⟨z0, hz0⟩ := hne
    let r : V → sourceSlab (ContinuousMap.id H) uv.1 uv.2 := fun z =>
      if hz : z ∈ K.space then ⟨q z, hmap hz⟩ else ⟨q z0, hmap hz0⟩
    have hrv (z : V) (hz : z ∈ K.space) : (r z : X) = q z := by
      simp only [r, dif_pos hz]
    have hr : PolyhedralPLInCharts d (fun z => (r z : X)) K.space :=
      hq.congr (fun z hz => (hrv z hz).symm)
    let T := standardSlabMeridianCoordinates uv.1 uv.2 m.ordered m.short
    let G : C(D × C, X) := ⟨fun z => (S.map (T z) : X), by fun_prop⟩
    have hPL := polyhedralPL_slab_parameter_of_period M.original_pl.source_domain hd
      uv.1 uv.2 m.ordered m.short G S.parameter S.parameter_pl S.period_eq K hK r hr
    apply hPL.congr
    intro z hz
    change (S.map (T (T.symm (r z))) : X) = f (q z)
    rw [T.apply_symm_apply]
    have heq : (⟨r z, sourceSlab_subset _ _ _ (r z).property⟩ : R) = q z :=
      Subtype.ext (hrv z hz)
    exact (hrestriction (r z)).symm.trans (congrArg (fun x : R => (f x : X)) heq)
  · have hempty : K.space = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    exact ⟨continuousOn_empty _, fun x => False.elim x.property⟩

end PoincareConjecture.M76.HamiltonIntervalTorus.StandardToSourceSlab
