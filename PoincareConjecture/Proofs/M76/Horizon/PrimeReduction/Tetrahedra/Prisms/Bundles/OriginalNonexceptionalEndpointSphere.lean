import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PhysicalPrismEndpointSphere
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalEndpointSphereProjection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRawPrismCoreHomeomorph









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 4000000 in
theorem exists_original_nonexceptional_endpoint_sphere
    {E X A ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [LocallyPathConnectedSpace A] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (g : E → X) (hg : ContinuousOn g K.space) (hgR : MapsTo g K.space R)
    (F : X → E) (hFc : Continuous F) (hFK : MapsTo F R K.space)
    (hFg : ∀ x ∈ K.space, F (g x) = x) (hgF : ∀ x ∈ R, g (F x) = x)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g (⋃ i,S i) s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (B : OriginalTetrahedralCutFamily K g (⋃ i,S i))
    (i₀ i₁ : ∀ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball, B.DiskIndex j.1.1)
    (hne : ∀ j, i₀ j ≠ i₁ j)
    (hcap : ∀ j, B.cut j.1.1 (i₀ j) ⊆ B.boundary j.1.1 j.1.2 ∧
      B.cut j.1.1 (i₁ j) ⊆ B.boundary j.1.1 j.1.2)
    (H : ∀ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
      (B.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ B.ball j.1.1 j.1.2)
    (hH : ∀ j, (H j).IsFinitePL)
    (hzero : ∀ j y, (H j y : E) ∈ B.cut j.1.1 (i₀ j) ↔ (y : E × ℝ).2 = 0)
    (hone : ∀ j y, (H j y : E) ∈ B.cut j.1.1 (i₁ j) ↔ (y : E × ℝ).2 = 1)
    (flip : ∀ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (B.ball j.1.1 j.1.2) → Bool)
    (hformula : ∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
      (B.ball j.1.1 j.1.2)) (u t : I),
      ((H j).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ)))
    (C : ∀ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
      (B.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (hC : ∀ j, (C j).IsFinitePL)
    (hCv : ∀ j x, (C j x : E) = H j (trimProduct (B.cut j.1.1 (i₀ j)) x))
    (O N : κ → Set X) (W : ∀ i, (A × unitInterval) ≃ₜ N i)
    (hO : ∀ i, IsOpen (O i)) (hON : ∀ i, O i ⊆ N i)
    (hOR : ∀ i, O i ⊆ R) (hSO : ∀ i, S i ⊆ O i)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (bad : Set (ConnectedComponents (K.space \ g ⁻¹' ⋃ i,S i : Set E)))
    (hbad : ∀ (s : K.FaceOfCard 3)
      (y : (convexHull ℝ (s.1 : Set E) \ ⋃ i,(D s).arc i : Set E)),
      ConnectedComponents.mk y ∈ (D s).exceptional →
      ∀ hy : (y : E) ∈ K.space \ g ⁻¹' ⋃ i,S i,
        ConnectedComponents.mk (⟨y,hy⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∈ bad)
    (p : (⋃ j,prismEnds (C j) : Set E))
    (hpbad : ∀ hp : (p : E) ∈ K.space \ g ⁻¹' ⋃ i,S i,
      ConnectedComponents.mk (⟨p,hp⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉ bad) :
    ∃ (r : E → E), FinitePiecewiseAffineOn r (⋃ j,prismTrim (H j)) ∧
      (∀ j x, r (C j x) = H j x) ∧
      ∃ i, ∃ Q : sphere (0 : V3) 1 ≃ₜ connectedComponentIn (⋃ j,prismEnds (C j)) (p : E),
        Q.IsFinitePL ∧ Q.symm.IsFinitePL ∧ ∀ z, r (Q z) = F ((sS i).parametrization z) := by
  classical
  let : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  let (t : K.FaceOfCard 4) : Finite (B.BallIndex t) := B.finite_ball t
  let : Finite (RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball) := by
    unfold RegularOriginalCutCell
    infer_instance
  have hgi : InjOn g K.space := by
    intro x hx y hy hxy
    exact (hFg x hx).symm.trans ((congrArg F hxy).trans (hFg y hy))
  have hcaps j y : g (H j y) ∈ ⋃ i,S i ↔
      (y : E × ℝ).2 = 0 ∨ (y : E × ℝ).2 = 1 := by
    have hcontact := B.regular_ball_cut_contact hK hgi D j (i₀ j) (i₁ j)
      (hne j) (hcap j).1 (hcap j).2
    have hm : (H j y : E) ∈ B.ball j.1.1 j.1.2 ∩ g ⁻¹' (⋃ i,S i) ↔
        (H j y : E) ∈ B.cut j.1.1 (i₀ j) ∪ B.cut j.1.1 (i₁ j) := by rw [hcontact]
    simpa only [mem_inter_iff,(H j y).property,true_and,mem_union,mem_preimage,hzero,hone] using hm
  have havoid : Disjoint (⋃ j,prismTrim (H j)) (g ⁻¹' ⋃ i,S i) := by
    apply disjoint_left.mpr
    rintro x hx hs
    obtain ⟨j,y,rfl⟩ := mem_iUnion.mp hx
    have ht := (hcaps j (trimProduct _ y)).mp hs
    have hb := trimInterval_mem ⟨(y : E × ℝ).2,y.property.2⟩
    change (trimInterval _ : ℝ) = 0 ∨ (trimInterval _ : ℝ) = 1 at ht
    rcases ht with ht | ht
    · linarith [hb.1]
    · linarith [hb.2]
  obtain ⟨r,hr,_,hrv,_,_,_,_⟩ := exists_original_endpoint_sphere_projection K hK g hgi D G
    hW hZ hL haffine B i₀ i₁ H hH hzero hone flip hformula C hC hCv havoid
  obtain ⟨Wraw,hWraw,_,_,_,_,_,_,_,_,hfamily⟩ := exists_original_raw_prism_core_homeomorph.{0}
    K hK g hgi D G hW hZ hL haffine B i₀ i₁ hne hcap H hzero hone flip hformula C hCv
    r hr.continuousOn hrv
  obtain ⟨Γ,hΓzero,hΓinto⟩ := hfamily p
  have hBK : (⋃ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
      B.ball j.1.1 j.1.2) ⊆ K.space := by
    rintro x ⟨_,⟨j,rfl⟩,hx⟩
    exact K.convexHull_subset_space j.1.1.2.1 (B.ball_subset_tetrahedron j.1.1 j.1.2 hx)
  have hpK : (p : E) ∈ K.space := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp p.property
    exact hBK (mem_iUnion.mpr ⟨j,prismTrim_subset (H j) (prismEnds_subset (C j) hj)⟩)
  have hpCut : (p : E) ∈ K.space \ g ⁻¹' ⋃ i,S i :=
    ⟨hpK,fun hs => disjoint_left.mp havoid
      (iUnion_mono (fun j => prismEnds_subset (C j)) p.property) hs⟩
  have hcover : connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E) ⊆
      (⋃ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
        B.ball j.1.1 j.1.2) \ g ⁻¹' ⋃ i,S i := by
    intro x hx
    have hxCut := connectedComponentIn_subset _ _ hx
    have hclass := (Topology.mem_componentIn_iff_component_class hpCut hxCut).mp hx
    have hxBad : ConnectedComponents.mk (⟨x,hxCut⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉ bad := by
      simpa only [hclass] using hpbad hpCut
    obtain ⟨j,hj⟩ := exists_regular_cell_of_component_not_mem_bad K g hgi hpure D B bad
      (fun s y hy => hbad s y hy _) ⟨x,hxCut⟩ hxBad
    exact ⟨mem_iUnion.mpr ⟨j,hj⟩,hxCut.2⟩
  refine ⟨r,hr,hrv,?_⟩
  exact exists_physical_prism_endpoint_sphere_from_raw_core g hg hgR F hFc hFK hFg hgF hF
    S sS hdis H C hC hBK r hr hrv hcaps Wraw hWraw O N W hO hON hOR hSO hcenter p
    hcover Γ hΓzero hΓinto

end PoincareConjecture.M76.PrismBelt
