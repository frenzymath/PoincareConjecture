import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalNoL3ComponentHomology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalCutFamilyEndpointCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalCoordinateCutHomology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalZeroHomologyExceptions

set_option autoImplicit false
open Set Metric Geometry CategoryTheory Limits
namespace PoincareConjecture.M76.PrismBelt
universe u
local notation "V3" => (Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
theorem OriginalTetrahedralCutFamily.exists_nonexceptional_cut_homology
    {E X : Type u} {A ι κ ν : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    [Finite κ] [Finite ν] {e : ι → OpenPartialHomeomorph X V3} {R Qcut : Set X}
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJK : J ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgR : MapsTo g K.space R)
    (F : X → E) (hFc : Continuous F) (hFK : MapsTo F R K.space)
    (hFg : ∀ x ∈ K.space, F (g x) = x) (hgF : ∀ x ∈ R, g (F x) = x)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hmark : ∀ z ∈ K.space, g z ∈ frontier R ↔ z ∈ J.space)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (hSR : (⋃ i,S i) ⊆ interior R)
    (B : OriginalTetrahedralCutFamily K g (⋃ i,S i))
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (a : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (ha : ∀ s, EqOn ((Q s) ∘ g) (a s) (convexHull ℝ (s.1 : Set E)))
    (havoid : Disjoint (⋃ i,S i) (g '' K.vertices))
    (hposition : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i,S i) g s.1 (a s))
    (O : κ → Set X) (W : ∀ i, (A × unitInterval) ≃ₜ closure (O i))
    (hO : ∀ i, IsOpen (O i)) (hCR : ∀ i, closure (O i) ⊆ R)
    (hSO : ∀ i, S i ⊆ O i)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hstrip : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hCC : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hQeq : Qcut = R \ ⋃ i,O i) (hQ : IsCompact Qcut) (hQPL : PLDomain e Qcut)
    (hno : HasNoPuncturedSphereComponents e F Qcut)
    (Sb : ν → Set X) (sSb : ∀ i, ChartwisePLSphere e (Sb i))
    (hbdis : Pairwise fun i j => Disjoint (Sb i) (Sb j))
    (hfront : frontier Qcut = frontier R ∪ ⋃ i,Sb i)
    (M : ModuleCat.{u} (ZMod 2)) [Nontrivial M] :
    ∃ bad : Set (ConnectedComponents (K.space \ g ⁻¹' ⋃ i,S i : Set E)),
      bad.Finite ∧ bad.ncard ≤ 4 * Nat.card (K.FaceOfCard 3) + J.vertices.ncard ∧
      (∀ (x : Qcut) (hxF : F x ∈ K.space \ g ⁻¹' ⋃ i,S i),
        ConnectedComponents.mk (⟨F x,hxF⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉ bad →
        ¬ IsZero ((TopCat.toSSet.obj (TopCat.of (connectedComponentIn Qcut (x : X)))).homology M 1)) ∧
      ∀ (Dcut : ConnectedComponents Qcut → Set X),
        (∀ x : Qcut, Dcut (ConnectedComponents.mk x) = connectedComponentIn Qcut (x : X)) →
        {c | IsZero ((TopCat.toSSet.obj (TopCat.of (Dcut c))).homology M 1)}.ncard ≤
          4 * Nat.card (K.FaceOfCard 3) + J.vertices.ncard := by
  classical
  have hgi : InjOn g K.space := by
    intro x hx y hy hxy
    exact (hFg x hx).symm.trans ((congrArg F hxy).trans (hFg y hy))
  obtain ⟨D,bad,hbadfin,hbound,hbad,G,_,hW,hZ,hL,haffine,i₀,i₁,hne,hcap,flip,
    H,hH,hzero,hone,hformula,C,hC,hCv,htrimavoid,_,_,_,_,τ,hτ,_,_,hτends,_⟩ :=
    B.exists_endpoint_cover hK hgi Q a hmap ha havoid hposition
  have hJS : Disjoint (g '' J.space) (⋃ i,S i) := by
    apply disjoint_left.mpr
    rintro _ ⟨y,hy,rfl⟩ hs
    exact ((hmark y (SimplicialComplex.space_subset_of_le hJK hy)).mpr hy).2 (hSR hs)
  obtain ⟨hbfin,hbbound⟩ := originalMarkedBoundaryComponents_finite_ncard K J hK hJK g (⋃ i,S i) hJS
  let total := bad ∪ originalMarkedBoundaryComponents K J g (⋃ i,S i)
  have htotalfin : total.Finite := hbadfin.union hbfin
  have htotalbound : total.ncard ≤ 4 * Nat.card (K.FaceOfCard 3) + J.vertices.ncard :=
    (ncard_union_le _ _).trans (Nat.add_le_add hbound hbbound)
  have hgood : ∀ (x : Qcut) (hxF : F x ∈ K.space \ g ⁻¹' ⋃ i,S i),
      ConnectedComponents.mk (⟨F x,hxF⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉ total →
      ¬ IsZero ((TopCat.toSSet.obj (TopCat.of (connectedComponentIn Qcut (x : X)))).homology M 1) := by
    intro x hxF hxgood
    have hxface : ConnectedComponents.mk (⟨F x,hxF⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉ bad :=
      fun h => hxgood (Or.inl h)
    obtain ⟨j,hj⟩ := exists_regular_cell_of_component_not_mem_bad K g hgi hpure D B bad hbad ⟨F x,hxF⟩ hxface
    let a₀ : B.cut j.1.1 (i₀ j) := ⟨((H j).symm ⟨F x,hj⟩ : E × ℝ).1,
      ((H j).symm ⟨F x,hj⟩).property.1⟩
    let p := prismEndpointLift C j a₀ false
    have hpball : (p : E) ∈ B.ball j.1.1 j.1.2 :=
      prismTrim_subset (H j) (prismEndMap (C j) a₀ false).property
    have hpraw : (p : E) ∈ K.space \ g ⁻¹' ⋃ i,S i :=
      ⟨K.convexHull_subset_space j.1.1.2.1 (B.ball_subset_tetrahedron j.1.1 j.1.2 hpball),
        fun hs => disjoint_left.mp htrimavoid
          (mem_iUnion.mpr ⟨j,(prismEndMap (C j) a₀ false).property⟩) hs⟩
    have hclass := B.component_class hgi j.1.1 j.1.2 ⟨F x,hxF⟩ ⟨p,hpraw⟩ hj hpball
    have hpface : ∀ hp : (p : E) ∈ K.space \ g ⁻¹' ⋃ i,S i,
        ConnectedComponents.mk (⟨p,hp⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉ bad := by
      intro hp
      simpa only [hclass] using hxface
    have hpboundary : ∀ hp : (p : E) ∈ K.space \ g ⁻¹' ⋃ i,S i,
        ConnectedComponents.mk (⟨p,hp⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉
          originalMarkedBoundaryComponents K J g (⋃ i,S i) := by
      intro hp hb
      exact hxgood (Or.inr (hclass ▸ hb))
    have hQR : Qcut ⊆ R := hQeq ▸ sdiff_subset
    have hQS : Disjoint Qcut (⋃ i,S i) := by
      apply disjoint_left.mpr
      intro y hy hs
      exact (hQeq.subset hy).2 (iUnion_mono hSO hs)
    have hxp : F x ∈ connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E) :=
      (Topology.mem_componentIn_iff_component_class hpraw hxF).mpr hclass.symm
    obtain ⟨_,_,_,_,i,r,hir,_⟩ := original_nonexceptional_noL3_component_homology_retract K J hK hpure
      g hg hgR F hFc hFK hFg hgF hF hmark S sS hdis hSR D G hW hZ hL haffine B i₀ i₁ hne hcap
      H hH hzero hone flip hformula C hC hCv O (fun i => closure (O i)) W hO
      (fun _ => subset_closure) (fun i => subset_closure.trans (hCR i)) hSO hcenter bad
      (fun s y hy _ => hbad s y hy) τ hτ hτends p hpface hpboundary hQ hQPL hQR hQS hno
      Sb sSb hbdis hfront x x.property hxp M
    obtain ⟨_,_,_,hnotzero⟩ := original_cut_component_homology_retract_of_raw_coordinates g hg.continuousOn
      hgR F hFc hFK hFg hgF O S W hQeq hQ.isClosed hCR hCC hstrip hcenter
      (fun i => (hSO i).trans subset_closure) p x x.property hxp M i r hir
    exact hnotzero
  refine ⟨total,htotalfin,htotalbound,hgood,?_⟩
  intro Dcut hDcut
  exact (ncard_zero_cut_components_le_original_exceptions g hg.continuousOn hgR F hFK hgF
    O S W hQeq hQ.isClosed hCR hCC hstrip hcenter hSO total htotalfin M hgood Dcut hDcut).trans htotalbound

end PoincareConjecture.M76.PrismBelt
