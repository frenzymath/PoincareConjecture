import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismCoreRescalingHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismEndpointCollarLift
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismEndpointInwardFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismEndpointComponentFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalTrimmedInterpolation



set_option autoImplicit false
open Set Geometry
open scoped Topology
universe w
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 700000 in
theorem exists_original_raw_prism_core_homeomorph
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (F : OriginalTetrahedralCutFamily K g S)
    (i₀ i₁ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (hne : ∀ j, i₀ j ≠ i₁ j)
    (hcap : ∀ j, F.cut j.1.1 (i₀ j) ⊆ F.boundary j.1.1 j.1.2 ∧
      F.cut j.1.1 (i₁ j) ⊆ F.boundary j.1.1 j.1.2)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (hzero : ∀ j y, (H j y : E) ∈ F.cut j.1.1 (i₀ j) ↔ (y : E × ℝ).2 = 0)
    (hone : ∀ j y, (H j y : E) ∈ F.cut j.1.1 (i₁ j) ↔ (y : E × ℝ).2 = 1)
    (flip : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (F.ball j.1.1 j.1.2) → Bool)
    (hformula : ∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
      (F.ball j.1.1 j.1.2)) (u t : I),
      ((H j).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ)))
    (C : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (hCv : ∀ j x, (C j x : E) = H j (trimProduct (F.cut j.1.1 (i₀ j)) x))
    (r : E → E) (hr : ContinuousOn r (⋃j,prismTrim (H j)))
    (hrv : ∀j y, r (C j y) = H j y) :
    ∃ W : ((⋃j,prismTrim (H j)) \ ⋃j,prismEnds (C j) : Set E) ≃ₜ
        ((⋃j : RegularOriginalCutCell K g S D F.BallIndex F.ball,F.ball j.1.1 j.1.2) \ g ⁻¹' S : Set E),
      (∀x, (W x : E) = r x) ∧
      (∀j (y : F.ball j.1.1 j.1.2) (hy : g y ∉ S),
        (W.symm ⟨y,mem_iUnion.mpr ⟨j,y.property⟩,hy⟩ : E) = C j ((H j).symm y)) ∧
      (∀ (γ : ℝ → E) (ε : ℝ), 0 < ε → ContinuousOn γ (Ioo 0 ε) →
        ContinuousAt γ 0 → g (γ 0) ∈ S →
        (∀ t ∈ Ioo 0 ε, γ t ∈
          (⋃ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,F.ball j.1.1 j.1.2) \ g ⁻¹' S) →
        ∃ (x : (⋃ j,prismEnds (C j))) (η : ℝ → (⋃ j,prismTrim (H j))),
          r x = γ 0 ∧ Filter.Tendsto η (𝓝[>] 0) (𝓝 (prismEndpointInclusion C x)) ∧
          ∀ t ∈ Ioo 0 ε, (η t : E) ∉ ⋃ j,prismEnds (C j) ∧ r (η t) = γ t) ∧
      (∀ {L : Type w} [TopologicalSpace L] [LocallyPathConnectedSpace L]
        (φ : C(L × ℝ,E)) (ε : ℝ), 0 < ε → (∀ a, g (φ (a,0)) ∈ S) →
        (∀ a t, t ∈ Ioo 0 ε → φ (a,t) ∈
          (⋃ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,F.ball j.1.1 j.1.2) \ g ⁻¹' S) →
        ∃ (σ : C(L,(⋃ j,prismEnds (C j)))) (η : L × ℝ → (⋃ j,prismTrim (H j))),
          (∀ a, r (σ a) = φ (a,0)) ∧
          (∀ a, Filter.Tendsto η (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 (prismEndpointInclusion C (σ a)))) ∧
          ∀ a t, t ∈ Ioo 0 ε → (η (a,t) : E) ∉ ⋃ j,prismEnds (C j) ∧
            r (η (a,t)) = φ (a,t)) ∧
      ∃ Γ : C((⋃ j,prismEnds (C j)) × I,K.space),
        (∀ p, (Γ (p,0) : E) = r p) ∧ (∀ p, g (Γ (p,0)) ∈ S) ∧
        (∀ p (t : I), 0 < (t : ℝ) → (t : ℝ) < 1 → g (Γ (p,t)) ∉ S) ∧
        (∀ {L : Type w} [TopologicalSpace L] {O K' : Set K.space}
          (W' : (L × I) ≃ₜ K'), IsOpen O → O ⊆ K' →
          (∀ z, g ((W' z : K.space) : E) ∈ S ↔ (z.2 : ℝ) = 1/2) →
          ∀ p : (⋃ j,prismEnds (C j)), Γ (p,0) ∈ O →
            ∃ (V : Set (⋃ j,prismEnds (C j))) (ε : ℝ) (positive : Bool),
            IsOpen V ∧ p ∈ V ∧ 0 < ε ∧ ε ≤ 1/2 ∧
            (∀ q ∈ V, ∀ t : I, (t : ℝ) < ε → Γ (q,t) ∈ O) ∧
            ∀ q ∈ V, ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < ε →
              ∀ z : L × I, (W' z : K.space) = Γ (q,t) →
                if positive then 1/2 < (z.2 : ℝ) else (z.2 : ℝ) < 1/2) ∧
        ∀ p : (⋃ j,prismEnds (C j) : Set E),
            ∃ Θ : C(connectedComponentIn (⋃ j,prismEnds (C j)) (p : E) × I,
                (⋃ j,prismTrim (H j))),
              (∀ q, (Θ (q,0) : E) = q) ∧
              ∀ q (t : I), 0 < (t : ℝ) → (t : ℝ) < 1 →
                (Θ (q,t) : E) ∉ ⋃ j,prismEnds (C j) ∧
                r (Θ (q,t)) ∈ connectedComponentIn (K.space \ g ⁻¹' S) (p : E) := by
  classical
  let : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  let (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  let : Finite (RegularOriginalCutCell K g S D F.BallIndex F.ball) := by
    unfold RegularOriginalCutCell
    infer_instance
  have hcaps j y : (H j y : E) ∈ g ⁻¹' S ↔
      (y : E × ℝ).2 = 0 ∨ (y : E × ℝ).2 = 1 := by
    have hcontact := F.regular_ball_cut_contact hK hgi D j (i₀ j) (i₁ j)
      (hne j) (hcap j).1 (hcap j).2
    have hm : (H j y : E) ∈ F.ball j.1.1 j.1.2 ∩ g ⁻¹' S ↔
        (H j y : E) ∈ F.cut j.1.1 (i₀ j) ∪ F.cut j.1.1 (i₁ j) := by rw [hcontact]
    simpa only [mem_inter_iff,(H j y).property,true_and,mem_union,hzero,hone] using hm
  have hcore : ∃ W : ((⋃j,prismTrim (H j)) \ ⋃j,prismEnds (C j) : Set E) ≃ₜ
      ((⋃j : RegularOriginalCutCell K g S D F.BallIndex F.ball,F.ball j.1.1 j.1.2) \ g ⁻¹' S : Set E),
      (∀x, (W x : E) = r x) ∧
      ∀j (y : F.ball j.1.1 j.1.2) (hy : g y ∉ S),
        (W.symm ⟨y,mem_iUnion.mpr ⟨j,y.property⟩,hy⟩ : E) = C j ((H j).symm y) :=
    exists_prism_core_rescaling_homeomorph
      (fun j => F.cut j.1.1 (i₀ j)) (fun j => F.ball j.1.1 j.1.2) (fun j => prismTrim (H j))
      (g ⁻¹' S) (fun j => (F.disk_pair j.1.1 (i₀ j)).isCompact) H C hcaps r hr hrv
      (original_raw_prism_rescaling_injOn K g hgi D G hW hZ hL haffine F i₀ H flip hformula C hCv r hrv)
  obtain ⟨W,hWvalue,hWinverse⟩ := hcore
  have havoid : Disjoint (⋃ j,prismTrim (H j)) (g ⁻¹' S) := by
    apply disjoint_left.mpr
    intro x hx hS
    obtain ⟨j,y,rfl⟩ := mem_iUnion.mp hx
    have he := (hcaps j (trimProduct _ y)).mp hS
    have hb := trimInterval_mem ⟨(y : E × ℝ).2,y.property.2⟩
    change (trimInterval _ : ℝ) = 0 ∨ (trimInterval _ : ℝ) = 1 at he
    rcases he with he | he
    · linarith [hb.1]
    · linarith [hb.2]
  obtain ⟨Γ,hΓ,hΓzero,hΓS,hΓaway⟩ := exists_prism_endpoint_inward_family H C
    (fun j => (F.disk_pair j.1.1 (i₀ j)).isCompact)
    (original_trimmed_interpolation_agrees K g hgi D G hW hZ hL haffine F i₀ H
      flip hformula C hCv havoid) hcaps r hr hrv
  have hΓspace (z : (⋃ j,prismEnds (C j)) × I) : Γ z ∈ K.space := by
    obtain ⟨j,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp z.1.property
    have hpoint : z.1 = prismEndpointLift C j a b := Subtype.ext hp.symm
    rw [show z = (z.1,z.2) from rfl,hpoint,hΓ]
    exact K.convexHull_subset_space j.1.1.2.1
      (F.ball_subset_tetrahedron j.1.1 j.1.2 (H j _).property)
  let Γ' : C((⋃ j,prismEnds (C j)) × I,K.space) :=
    ⟨fun z => ⟨Γ z,hΓspace z⟩,Γ.continuous.subtype_mk _⟩
  refine ⟨W,hWvalue,hWinverse,?_,?_,Γ',hΓzero,hΓS,hΓaway,?_,?_⟩
  · intro γ ε hε hγ hγ0 hγS hinto
    exact exists_prism_endpoint_lift_of_core_path H C
      (fun j => (F.disk_pair j.1.1 (i₀ j)).isCompact) r hr hrv W hWvalue
      hε hγ hγ0 hγS hinto
  · intro L _ _ φ ε hε hzero hinto
    exact exists_prism_endpoint_collar_lift H C
      (fun j => (F.disk_pair j.1.1 (i₀ j)).isCompact) r hr hrv W hWvalue
      φ hε hzero hinto
  · intro L _ O K' W' hO hOK hcenter p hp
    exact exists_endpoint_neighborhood_collar_side
      (S := {x : K.space | g x ∈ S}) W' hO hOK hcenter Γ' hΓaway p hp
  · intro p
    obtain ⟨y₀,_,Θ,hΘzero,hmid,hΘinto⟩ := exists_prism_endpoint_component_inward_family H C
      (fun j => (F.disk_pair j.1.1 (i₀ j)).isCompact)
      (original_trimmed_interpolation_agrees K g hgi D G hW hZ hL haffine F i₀ H
        flip hformula C hCv havoid) hcaps r hr hrv p
    have hsub : ((⋃ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
        F.ball j.1.1 j.1.2) \ g ⁻¹' S : Set E) ⊆ K.space \ g ⁻¹' S := by
      rintro x ⟨hx,hs⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact ⟨K.convexHull_subset_space j.1.1.2.1
        (F.ball_subset_tetrahedron j.1.1 j.1.2 hj),hs⟩
    have htrim : (⋃ j,prismTrim (H j)) ⊆ K.space \ g ⁻¹' S := by
      intro z hz
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      exact hsub ⟨mem_iUnion.mpr ⟨j,prismTrim_subset (H j) hj⟩,
        fun hs => disjoint_left.mp havoid hz hs⟩
    obtain ⟨j,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp p.property
    have hp' : p = prismEndpointLift C j a b := Subtype.ext hp.symm
    let mid : (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) :=
      ⟨(a,(1/2 : ℝ)),a.property,by norm_num⟩
    have hmidfixed : trimProduct _ mid = mid := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · norm_num [trimProduct,trimInterval,mid]
    have hmidvalue : y₀ = C j mid := by
      rw [hmid j a b hp',hCv,hmidfixed]
    let γ : I → E := fun t => C j ⟨(a,t),a.property,t.property⟩
    have hγ : Continuous γ := continuous_subtype_val.comp ((C j).continuous.comp
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _))
    have hbase : (p : E) ∈ range γ := by
      rw [hp']
      exact ⟨⟨if b then 1 else 0,by cases b <;> norm_num⟩,rfl⟩
    have hy₀ : y₀ ∈ connectedComponentIn (K.space \ g ⁻¹' S) (p : E) := by
      apply (isPreconnected_range hγ).subset_connectedComponentIn hbase
        (by rintro z ⟨t,rfl⟩; exact htrim (mem_iUnion.mpr ⟨j,(C j _).property⟩))
      exact ⟨⟨1/2,by norm_num⟩,hmidvalue.symm⟩
    refine ⟨Θ,hΘzero,?_⟩
    intro q t ht ht1
    exact ⟨(hΘinto q t ht ht1).1,
      (connectedComponentIn_eq hy₀).symm.subset
        (connectedComponentIn_mono y₀ hsub (hΘinto q t ht ht1).2)⟩

end PoincareConjecture.M76.PrismBelt
