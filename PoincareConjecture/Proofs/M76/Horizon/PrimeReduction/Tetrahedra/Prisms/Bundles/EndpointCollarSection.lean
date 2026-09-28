import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointBoundaryLift
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointLimitPath
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCollarSideUniqueness



set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt

theorem exists_collar_section_through_endpoint
    {X Y A : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    {D : Set X} {B M S O K : Set Y} (f : X → Y) (hf : Continuous f)
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (W : (A × unitInterval) ≃ₜ K) (a : A)
    (hO : IsOpen O) (hOK : O ⊆ K) (hOM : O ⊆ M)
    (hcenter : ∀ z, (W z : Y) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (hcenterO : ∀ b, (W (b,⟨1/2,by norm_num,by norm_num⟩) : Y) ∈ O)
    (y₀ : Y) (hcover : connectedComponentIn (M \ S) y₀ ⊆ B)
    (γ : C(unitInterval,X))
    (hstart : f (γ 0) = W (a,⟨1/2,by norm_num,by norm_num⟩))
    (hfinite : ∀ b, (f ⁻¹' {(W (b,⟨1/2,by norm_num,by norm_num⟩) : Y)}).Finite)
    (hinto : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      γ t ∈ D ∧ f (γ t) ∈ connectedComponentIn (M \ S) y₀) :
    ∃ (u : Set A) (_hu : IsOpen u) (ha : a ∈ u)
      (σ : C(u,connectedComponentIn (f ⁻¹' S) (γ 0))),
      (σ ⟨a,ha⟩ : X) = γ 0 ∧
      (∀ b, f (σ b) = W (b,⟨1/2,by norm_num,by norm_num⟩)) ∧ IsPathConnected u := by
  let m : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  let γ' : C(unitInterval,Y) := ⟨fun t => f (γ t),hf.comp γ.continuous⟩
  have hcenter' (z : A × unitInterval) : (W z : Y) ∈ S ∩ O ↔ (z.2 : ℝ) = 1/2 := by
    constructor
    · exact fun hz => (hcenter z).mp hz.1
    · intro hz
      have he : z.2 = m := Subtype.ext hz
      refine ⟨(hcenter z).mpr hz,?_⟩
      have hzO := hcenterO z.1
      change (W (z.1,m) : Y) ∈ O at hzO
      simpa only [← he] using hzO
  obtain ⟨ε,positive,hε,hεhalf,_hnear,hside⟩ :=
    exists_endpoint_path_collar_side W hO hOK inter_subset_right hcenter' γ'
      (by change f (γ 0) ∈ S ∩ O; rw [hstart]; exact ⟨(hcenter _).mpr rfl,hcenterO a⟩)
      (fun t ht ht1 hs => (connectedComponentIn_subset (M \ S) y₀ (hinto t ht ht1).2).2 hs.1)
  obtain ⟨u,lo,hi,hu,hau,hupath,hlo,hhi,hrect,hhalves⟩ :=
    exists_connected_collar_half_neighborhoods W a hO isOpen_univ hcenter ⟨mem_univ _,hcenterO a⟩
  obtain ⟨δ,hδ,hδhalf,hδrect⟩ := exists_path_mem_collar_rectangle W hO hOK hu γ' (a,m)
    ⟨hau,hlo,hhi⟩ hstart (by change f (γ 0) ∈ O; rw [hstart]; exact hcenterO a)
  let e := min ε δ
  have he : 0 < e := lt_min hε hδ
  have hehalf : e ≤ 1/2 := (min_le_left _ _).trans hεhalf
  let t₀ : unitInterval := ⟨e/2,by linarith,by linarith⟩
  have ht₀ : 0 < (t₀ : ℝ) ∧ (t₀ : ℝ) < e := by
    change 0 < e/2 ∧ e/2 < e
    constructor <;> linarith
  let C : Set Y := (fun z => (W z : Y)) ''
    (u ×ˢ (if positive then Ioo m hi else Ioo lo m))
  have hC : IsPreconnected C := (hhalves positive).1
  have hCM : C ⊆ M \ S := fun _ hx =>
    ⟨hOM ((hhalves positive).2 hx).1.2,((hhalves positive).2 hx).2⟩
  have htC : f (γ t₀) ∈ C := by
    obtain ⟨z,hz,hzval⟩ := hδrect t₀ (ht₀.2.trans_le (min_le_right _ _))
    refine ⟨z,⟨hz.1,?_⟩,hzval⟩
    have hs := hside t₀ ht₀.1 (ht₀.2.trans_le (min_le_left _ _)) z hzval
    cases positive
    · exact ⟨hz.2.1,hs⟩
    · exact ⟨hs,hz.2.2⟩
  have hCcomp : C ⊆ connectedComponentIn (M \ S) y₀ := by
    have hh := hC.subset_connectedComponentIn htC hCM
    rwa [← connectedComponentIn_eq (hinto t₀ ht₀.1 (ht₀.2.trans_le
      (hehalf.trans (by norm_num)))).2] at hh
  have hCB : C ⊆ B := hCcomp.trans hcover
  let d : ℝ := min ((hi : ℝ) - 1/2) (1/2 - (lo : ℝ))
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  let τ (t : ℝ) : unitInterval := projIcc 0 1 zero_le_one
    (if positive then 1/2+t else 1/2-t)
  have hτcont : Continuous τ := by
    unfold τ
    cases positive <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
  have hτzero : τ 0 = m := by
    apply Subtype.ext
    cases positive <;> norm_num [τ,m,projIcc]
  have hτ (t : ℝ) (ht : t ∈ Ioo 0 d) :
      τ t ∈ (if positive then Ioo m hi else Ioo lo m) := by
    have hh : t < (hi : ℝ) - 1/2 := ht.2.trans_le (min_le_left _ _)
    have hl : t < 1/2 - (lo : ℝ) := ht.2.trans_le (min_le_right _ _)
    cases positive
    · have hmem : 1/2-t ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [lo.property.1,ht.1]
      simp only [τ,Bool.false_eq_true,ite_false]
      rw [projIcc_of_mem zero_le_one hmem]
      constructor
      · change (lo : ℝ) < 1/2-t
        linarith
      · change 1/2-t < 1/2
        linarith [ht.1]
    · have hmem : 1/2+t ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hi.property.2,ht.1]
      simp only [τ,ite_true]
      rw [projIcc_of_mem zero_le_one hmem]
      constructor
      · change 1/2 < 1/2+t
        linarith [ht.1]
      · change 1/2+t < (hi : ℝ)
        linarith
  let φ : C(u × ℝ,Y) := ⟨fun z => W (z.1,τ z.2),
    continuous_subtype_val.comp (W.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (hτcont.comp continuous_snd)))⟩
  have hφzero (b : u) : φ (b,0) = W (b,m) := by change (W (_,τ 0) : Y) = _; rw [hτzero]
  have hφC (b : u) (t : ℝ) (ht : t ∈ Ioo 0 d) : φ (b,t) ∈ C :=
    ⟨(b,τ t),⟨b.property,hτ t ht⟩,rfl⟩
  let : LocallyPathConnectedSpace u := hu.locallyPathConnectedSpace
  obtain ⟨σ,η,hσ,hlim,hη,hηcont⟩ := exists_continuous_core_inverse_boundary_lift hf H hH
    φ hd (fun b t ht => hCB (hφC b t ht)) (fun b => by rw [hφzero]; exact hfinite b)
  let a₀ : u := ⟨a,hau⟩
  have hηa : ContinuousOn (fun t : ℝ => η (a₀,t)) (Ioo 0 d) :=
    hηcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨mem_univ _,ht⟩)
  have hηlim : Tendsto (fun t : ℝ => η (a₀,t)) (𝓝[>] 0) (𝓝 (σ a₀)) :=
    (hlim a₀).comp (tendsto_const_nhds.prodMk tendsto_id)
  obtain ⟨ξ,hξzero,hξval⟩ := exists_path_of_endpoint_limit hd hηa hηlim
  have htime (t : unitInterval) (ht : 0 < (t : ℝ)) : d/2 * (t : ℝ) ∈ Ioo 0 d := by
    constructor
    · positivity
    · nlinarith [t.property.2]
  have hξf (t : unitInterval) (ht : 0 < (t : ℝ)) : f (ξ t) = φ (a₀,d/2*t) := by
    rw [hξval t ht,hη a₀ _ (htime t ht),hH,H.apply_symm_apply]
  have hξD (t : unitInterval) (ht : 0 < (t : ℝ)) : ξ t ∈ D := by
    rw [hξval t ht,hη a₀ _ (htime t ht)]
    exact (H.symm _).property
  have hξstart : f (ξ 0) = W (a,m) := by rw [hξzero,hσ,hφzero]
  let paths (b : Bool) := if b then ξ else γ
  have hpaths (b : Bool) : f (paths b 0) = W (a,m) := by
    cases b
    · exact hstart
    · exact hξstart
  have heq := endpoint_eq_of_same_original_collar_side f hf H hH W a hO hOK hOM hcenter
    (hcenterO a) y₀ hcover paths hpaths (by rw [hpaths false]; exact hfinite a)
    (by
      intro b t ht ht1
      cases b
      · exact hinto t ht (ht1.trans (by norm_num))
      · refine ⟨hξD t ht,?_⟩
        change f (ξ t) ∈ _
        rw [hξf t ht]
        exact hCcomp (hφC a₀ _ (htime t ht))) ε hε positive (by
      intro b t ht hte z hz
      cases b
      · exact hside t ht hte z hz
      · change (W z : Y) = f (ξ t) at hz
        rw [hξf t ht] at hz
        have hv : z = (a,τ (d/2*t)) := W.injective (Subtype.ext hz)
        rw [hv]
        have hs := hτ _ (htime t ht)
        cases positive
        · exact hs.2
        · exact hs.1)
  have hthrough : σ a₀ = γ 0 := hξzero.symm.trans heq.symm
  let : PreconnectedSpace u := isPreconnected_iff_preconnectedSpace.mp
    hupath.isConnected.isPreconnected
  have hσcomp : σ '' univ ⊆ connectedComponentIn (f ⁻¹' S) (γ 0) := by
    apply (isPreconnected_univ.image σ σ.continuous.continuousOn).subset_connectedComponentIn
      ⟨a₀,mem_univ _,hthrough⟩
    rintro x ⟨b,_,rfl⟩
    change f (σ b) ∈ S
    rw [hσ,hφzero]
    exact (hcenter _).mpr rfl
  let σ' : C(u,connectedComponentIn (f ⁻¹' S) (γ 0)) :=
    ⟨fun b => ⟨σ b,hσcomp (mem_image_of_mem σ (mem_univ b))⟩,σ.continuous.subtype_mk _⟩
  exact ⟨u,hu,hau,σ',hthrough,fun b => (hσ b).trans (hφzero b),hupath⟩

end PoincareConjecture.M76.PrismBelt
