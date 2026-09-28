import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.PrescribedIrreducibleCappedDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalExteriorNonspherical









set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Metric Geometry Geometry.SeparatedSphereCaps
namespace PoincareConjecture.M76
universe u v
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_irreducible_capped_exterior_from_cut
    {ι : Type u} {κ : Type v} {α E : Type*} {ν : Type (max u v)}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)} (bD : HamiltonMarkedProtectedBall ι κ L e D)
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (c : MarkedSphereCut e (closure (latticeHandleDomain ι κ L \ D)) ν)
    {f : LatticeHandleAmbient ι κ L → E} (K : SimplicialComplex ℝ E)
    (g : E → LatticeHandleAmbient ι κ L)
    (hgPL : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ closure (latticeHandleDomain ι κ L \ D),f x ∈ K.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f c.carrier)
    (hmax : ∀ (μ : Type (max u v)) [Fintype μ]
      (d : MarkedSphereCut e (closure (latticeHandleDomain ι κ L \ D)) μ),
      HasNoPuncturedSphereComponents e f d.carrier → Fintype.card μ ≤ Fintype.card ν)
    {U : Set (LatticeHandleAmbient ι κ L)}
    (hU : IsOpen U) (hSU : ∀ i,c.spheres i ⊆ U) :
    ∃ cut : MarkedSphereCut e (closure (latticeHandleDomain ι κ L \ D)) ν,
      cut.spheres = c.spheres ∧ c.carrier ⊆ cut.carrier ∧
      closure (⋃ i,cut.collar i) ⊆ U ∧
      HasNoPuncturedSphereComponents e f cut.carrier ∧
      ∃ P : Set (LatticeHandleAmbient ι κ L),IsCompact P ∧
        closure (latticeHandleDomain ι κ L \ D) ⊆ interior P ∧ PLDomain e P ∧
    ∃ (τ : Type (max u v)) (_ : Fintype τ)
      (F : LatticeHandleAmbient ι κ L → (τ → ℝ × V3))
      (W : Set ((τ → ℝ × V3) × ((ν × Bool) → ℝ))),
      let caps : ν × Bool → Set ((τ → ℝ × V3) × ((ν × Bool) → ℝ)) :=
        fun j => cap j (F '' cut.ports j)
      let Dc := lift '' (F '' cut.carrier) ∪ ⋃ j, caps j
      let Qouter := P \ ⋃ i,cut.collar i
      PLDomain e Qouter ∧ frontier Qouter = frontier P ∪ ⋃ j,cut.ports j ∧
      IsCompact Qouter ∧
      InjOn F Qouter ∧
      W = (lift '' (F '' Qouter) ∪ ⋃ j,caps j) \ lift '' (F '' frontier P) ∧
      (∀ j,caps j ∩ lift '' (F '' Qouter) = lift '' (F '' cut.ports j)) ∧
      (∀ x ∈ Qouter,∃ (j : α) (V : Set (LatticeHandleAmbient ι κ L))
          (a : (τ → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e j).source ∧ EqOn (a ∘ F) (e j) V) ∧
      (∃ K : SimplicialComplex ℝ (τ → ℝ × V3),K.faces.Finite ∧ K.space = F '' Qouter) ∧
      Disjoint (lift '' (F '' frontier P)) (⋃ j,caps j) ∧
      Dc ⊆ W ∧ Continuous F ∧
      (∀ j, LocallyPiecewiseAffineOn (F ∘ (e j).symm) (e j).target) ∧
      InjOn F cut.carrier ∧
      (∀ j, IsFinitePLBallPair V3 (caps j) (lift '' (F '' cut.ports j))) ∧
      (∀ j, caps j ∩ lift '' (F '' cut.carrier) = lift '' (F '' cut.ports j)) ∧
      Pairwise (fun i j => Disjoint (caps i) (caps j)) ∧
      ∃ atlas : W → OpenPartialHomeomorph W V3,
        (∀ p : W, p ∈ (atlas p).source) ∧ PLDomain atlas univ ∧
        (∀ p : W, ∃ (B : Set ((τ → ℝ × V3) × ((ν × Bool) → ℝ)))
          (a : ((τ → ℝ × V3) × ((ν × Bool) → ℝ)) → V3)
          (a' : V3 → ((τ → ℝ × V3) × ((ν × Bool) → ℝ))),
          FinitePiecewiseAffineOn a B ∧
          FinitePiecewiseAffineOn a' (closedBall (0 : V3) 1) ∧
          (∀ x ∈ (atlas p).source,
            (x : (τ → ℝ × V3) × ((ν × Bool) → ℝ)) ∈ B ∧ atlas p x = a x) ∧
          (atlas p).target ⊆ interior (closedBall (0 : V3) 1) ∧
          ∀ y ∈ (atlas p).target,
            ((atlas p).symm y : (τ → ℝ × V3) × ((ν × Bool) → ℝ)) = a' y) ∧
        let val : W → ((τ → ℝ × V3) × ((ν × Bool) → ℝ)) := Subtype.val
        IsPLIrreducible atlas (val ⁻¹' Dc) ∧ IsCompact (val ⁻¹' Dc) ∧
        frontier (val ⁻¹' Dc) = val ⁻¹' (lift '' (F '' frontier (closure (latticeHandleDomain ι κ L \ D)))) ∧
        (∀ j, Nonempty (ChartwisePLBall atlas
          (val ⁻¹' caps j) (val ⁻¹' lift '' (F '' cut.ports j)))) ∧
        (∀ j, val ⁻¹' caps j ⊆ interior (val ⁻¹' Dc)) := by
  classical
  obtain ⟨hR,hsub,_,_,_,_,_⟩ := bD.closed_complement_geometry he hdim hi
  have heR := bD.plDomain_closed_complement he hdim hi
  obtain ⟨cut,hcutS,hmono,hsupport,hnoCut,P,hP,hRP,heP,τ,hτ,F,W,
    heQouter,hfrontQouter,hQouter,
    houterInj,hW,houterAttach,hproj,houterModel,houterDis,
    hDW,hFc,hF,hFi,hcaps,hcontact,hcapsdis,atlas,hcenter,hatlas,hrep,
    heD,hD,hDf,hcapBalls,hcapsInterior,htest⟩ :=
    exists_maximal_capped_sphere_cut_from_cut hR heR c K g hgPL hgi hreal hno hmax hU hSU
  let := hτ
  refine ⟨cut,hcutS,hmono,hsupport,hnoCut,P,hP,hRP,heP,τ,hτ,F,W,
    heQouter,hfrontQouter,hQouter,
    houterInj,hW,houterAttach,hproj,houterModel,houterDis,
    hDW,hFc,hF,hFi,hcaps,hcontact,hcapsdis,
    atlas,hcenter,hatlas,hrep,⟨heD,?_⟩,hD,hDf,hcapBalls,hcapsInterior⟩
  rintro S hS ⟨sS⟩
  by_contra hnot
  obtain ⟨G,V,hV,hVD,hfix,hGPL,hGinv,hGS,hclear,T,sT,hT,himage,hnotT,
    d,x,hdS,hdO,hdB,hdC,hdinside,⟨raw⟩,hx,hpunctured,hnotPorts,side,hchosen,hcases⟩ :=
    htest S sS hS hnot
  have hCd := connectedComponentIn_subset d.carrier x
  have hdc : d.carrier ⊆ cut.carrier := hdC.subset.trans sdiff_subset
  have hTdomain : T ⊆ closure (latticeHandleDomain ι κ L \ D) :=
    hT.trans (interior_subset.trans fun _ h => h.1)
  have hsep := raw.not_both_ports_subset_of_lattice L sT he hdim (hTdomain.trans hsub)
    isPreconnected_connectedComponentIn (fun z hz => (hdC.subset (hCd hz)).2)
  rcases hcases with ⟨hother,_⟩ | ⟨hopposite,_⟩
  · apply hsep
    cases side
    · exact ⟨hchosen,hother⟩
    · exact ⟨hother,hchosen⟩
  obtain ⟨hC,_,_,_,hfront⟩ := d.punctured_component_port_boundary
    (fun S s hS => bD.no_sphere_in_exterior_frontier he hdim hi hS ⟨s⟩) K g hgPL hgi hreal hx hpunctured
  let phi : LatticeHandleAmbient ι κ L → ((τ → ℝ × V3) × ((ν × Bool) → ℝ)) :=
    fun x => lift (F x)
  have hphiPL j : LocallyPiecewiseAffineOn (phi ∘ (e j).symm) (e j).target :=
    (hF j).prod_mk (locallyPiecewiseAffineOn_affine
      (ContinuousAffineMap.const ℝ V3 (0 : (ν × Bool) → ℝ)) (e j).open_target)
  have hphii : InjOn phi cut.carrier := by
    intro x hx y hy hxy
    exact hFi hx hy (congrArg Prod.fst hxy)
  have hrep' (p : W) : ∃ (B : Set ((τ → ℝ × V3) × ((ν × Bool) → ℝ)))
      (a : ((τ → ℝ × V3) × ((ν × Bool) → ℝ)) → V3),
      FinitePiecewiseAffineOn a B ∧
      ∀ x ∈ (atlas p).source, (x : (τ → ℝ × V3) × ((ν × Bool) → ℝ)) ∈ B ∧
        atlas p x = a x := by
    obtain ⟨B,a,a',ha,ha',hvalues,_,_⟩ := hrep p
    exact ⟨B,a,ha,hvalues⟩
  apply hnot
  simpa only [phi, image_image] using
    cut.exists_ball_of_single_new_port_component d (fun j => hdB j.1 j.2)
    hdc hC.isClosed hCd hpunctured hfront side hchosen hopposite raw K
    g hgPL hgi hreal phi
    (hFc.prodMk continuous_const) hphiPL hphii (fun j => cap j (F '' cut.ports j))
    (by simpa only [phi, image_image] using hcaps)
    (by simpa only [phi, image_image] using hcontact) hcapsdis
    (by simpa only [phi, image_image] using hDW)
    atlas (fun p => ⟨p,hcenter p⟩) hatlas.compatible hrep' G (S := S)
    (by simpa only [phi, image_image] using hVD.trans interior_subset) hfix hGinv
    (by simpa only [phi, image_image] using himage)

end PoincareConjecture.M76
