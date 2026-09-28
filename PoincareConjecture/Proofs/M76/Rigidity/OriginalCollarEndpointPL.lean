import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetTranslationPL
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapsePhasePL
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteLabelSubcomplex
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGluing
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))





theorem ChartwisePLMap.polyhedralPL_hamiltonZeroAmbientMap_comp
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {u : E → X0} (hu : PolyhedralPLInCharts e u K.space) :
    PolyhedralPLInCharts d (fun x => hamiltonZeroAmbientMap phi (u x)) K.space := by
  let q : E → R0 := fun x => ⟨u x, by rw [hamiltonZeroDomain_eq_univ]; trivial⟩
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hu.continuousOn
  have hcomp := hphi.polyhedralPLInCharts_comp K hK q hq hu
    (fun _ _ => mem_univ _)
  apply hcomp.congr
  intro x hx
  change hamiltonZeroAmbientEquiv.symm
    (phi (latticeHandleDomainEquiv (Fin 0) (Fin 3) L0 (q x))) = _
  rw [← hamiltonZeroAmbientEquiv_domain (q x)]
  rfl

open Classical in





theorem polyhedralPL_hamiltonZero_collar_endpoint
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    {c : E × ℝ → X0}
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-1 : ℝ) 1))
    {delta r : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) (hr : 0 ≤ r)
    (a b : C0)
    (hlabels : ∀ x ∈ L.space,
      hamiltonZeroCircleMap phi (c (x, 0)) ∈ ({a, b} : Set C0)) :
    PolyhedralPLInCharts d
      (fun z => hamiltonZeroTargetTranslation
        ((if hamiltonZeroCircleMap phi (c (z.1, 0)) = a then 1 else -1) *
            CollarCollapse.displacement r z.2,
          hamiltonZeroAmbientMap phi (c (z.1, CollarCollapse.height r z.2))))
      (L.space ×ˢ Icc (-delta) delta) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨K, hK, hKspace⟩ := L.exists_finite_interval_product hL
    (show -delta < delta by linarith)
  have hu : FinitePiecewiseAffineOn (fun z : E × ℝ => z.1) K.space :=
    (K.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have ht : FinitePiecewiseAffineOn (fun z : E × ℝ => z.2) K.space :=
    (K.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hcollapse := CollarCollapse.finitePiecewiseAffineOn_collapse_pair hu ht r
  have hmap : MapsTo (fun z : E × ℝ => (z.1, CollarCollapse.height r z.2))
      K.space (L.space ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz
    have hz' := hKspace.subset hz
    have hh : CollarCollapse.height r z.2 ∈ Icc (-delta) delta := by
      simpa only [CollarCollapse.move_one] using
        CollarCollapse.move_mem_Icc (s := 1) hr (by norm_num) hz'.2
    exact ⟨hz'.1, by linarith [hh.1], hh.2.trans hdeltaOne⟩
  have hsource := hc.comp_finitePiecewiseAffineOn K hK hcollapse hmap
  have hY := hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hsource
  let label : E × ℝ → C0 := fun z => hamiltonZeroCircleMap phi (c (z.1, 0))
  have hzero : MapsTo (fun z : E × ℝ => (z.1, (0 : ℝ)))
      K.space (L.space ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz
    exact ⟨(hKspace.subset hz).1, by norm_num⟩
  have hlabel : ContinuousOn label K.space :=
    (hamiltonZeroCircleMap phi).continuous.comp_continuousOn
      (hc.continuousOn.comp
        (continuous_fst.prodMk continuous_const).continuousOn hzero)
  have hlabelsK : MapsTo label K.space ({a, b} : Set C0) := by
    intro z hz
    exact hlabels z.1 (hKspace.subset hz).1
  let J : C0 → SimplicialComplex ℝ (E × ℝ) := fun v =>
    K.vertexSubcomplex {z | label z = v}
  have hJ (v : C0) : (J v).faces.Finite := K.vertexSubcomplex_finite _ hK
  have hJspace (v : C0) : (J v).space = K.space ∩ label ⁻¹' {v} :=
    K.vertexSubcomplex_space_eq_finite_label hlabel
      ((finite_singleton b).insert a) hlabelsK v
  let w : E × ℝ → ℝ := fun z =>
    (if label z = a then 1 else -1) * CollarCollapse.displacement r z.2
  have hwphase (v : C0) : FinitePiecewiseAffineOn w (J v).space := by
    have htJ := ht.restrict (J v) (hJ v) (fun z hz => ((hJspace v).subset hz).1)
    have hs := CollarCollapse.finitePiecewiseAffineOn_scaled_displacement
      htJ r (if v = a then 1 else -1)
    apply hs.congr
    intro z hz
    have hv : label z = v := ((hJspace v).subset hz).2
    dsimp only [w]
    rw [hv]
  have hcover : K.space = (J a).space ∪ (J b).space :=
    K.two_label_subcomplex_cover hlabel a b hlabelsK
  have hw : FinitePiecewiseAffineOn w K.space := by
    rw [hcover]
    exact (hwphase a).union (hwphase b) K hK hcover
  simpa only [hKspace, w, label, Function.comp_def] using
    hd.polyhedralPL_hamiltonZeroTargetTranslation hY hw

end PoincareConjecture.M76
