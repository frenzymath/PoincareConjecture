import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismEndpointSphere

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_physical_prism_endpoint_sphere_from_raw_core
    {E X A ι κ η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [LocallyPathConnectedSpace A] [Finite κ] [Finite η]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {K₀ : Set E}
    (g : E → X) (hg : ContinuousOn g K₀) (hgR : MapsTo g K₀ R)
    (F : X → E) (hFc : Continuous F) (hFK : MapsTo F R K₀)
    (hFg : ∀ x ∈ K₀, F (g x) = x) (hgF : ∀ x ∈ R, g (F x) = x)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {Ac Bc Tc : η → Set E}
    (Hc : ∀ j, (Ac j ×ˢ I : Set (E × ℝ)) ≃ₜ Bc j)
    (C : ∀ j, (Ac j ×ˢ I : Set (E × ℝ)) ≃ₜ Tc j)
    (hC : ∀ j, (C j).IsFinitePL) (hBK : (⋃ j,Bc j) ⊆ K₀)
    (r : E → E) (hr : FinitePiecewiseAffineOn r (⋃ j,Tc j))
    (hrv : ∀ j x, r (C j x) = Hc j x)
    (hcap : ∀ j x, g (Hc j x) ∈ ⋃ i,S i ↔
      (x : E × ℝ).2 = 0 ∨ (x : E × ℝ).2 = 1)
    (Wraw : ((⋃ j,Tc j) \ ⋃ j,prismEnds (C j) : Set E) ≃ₜ
      ((⋃ j,Bc j) \ g ⁻¹' ⋃ i,S i : Set E))
    (hWraw : ∀ x, (Wraw x : E) = r x)
    (O K : κ → Set X) (W : ∀ i, (A × unitInterval) ≃ₜ K i)
    (hO : ∀ i, IsOpen (O i)) (hOK : ∀ i, O i ⊆ K i)
    (hOR : ∀ i, O i ⊆ R) (hSO : ∀ i, S i ⊆ O i)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (p : (⋃ j,prismEnds (C j) : Set E))
    (hcover : connectedComponentIn (K₀ \ g ⁻¹' ⋃ i,S i) (p : E) ⊆
      (⋃ j,Bc j) \ g ⁻¹' ⋃ i,S i)
    (Γ : C(connectedComponentIn (⋃ j,prismEnds (C j)) (p : E) × I,(⋃ j,Tc j)))
    (hΓzero : ∀ q, (Γ (q,0) : E) = q)
    (hΓinto : ∀ q (t : I), 0 < (t : ℝ) → (t : ℝ) < 1 →
      (Γ (q,t) : E) ∉ ⋃ j,prismEnds (C j) ∧
      r (Γ (q,t)) ∈ connectedComponentIn (K₀ \ g ⁻¹' ⋃ i,S i) (p : E)) :
    ∃ i, ∃ Q : sphere (0 : V3) 1 ≃ₜ connectedComponentIn (⋃ j,prismEnds (C j)) (p : E),
      Q.IsFinitePL ∧ Q.symm.IsFinitePL ∧ ∀ z, r (Q z) = F ((sS i).parametrization z) := by
  let U := (⋃ j,Tc j : Set E)
  let Ends := (⋃ j,prismEnds (C j) : Set E)
  let V := ((⋃ j,Bc j) \ g ⁻¹' ⋃ i,S i : Set E)
  let D : Set U := {x | (x : E) ∉ Ends}
  have hVK : V ⊆ K₀ := fun _ hx => hBK hx.1
  have hrmap : MapsTo r U (⋃ j,Bc j) := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    have hval := hrv j ((C j).symm ⟨x,hj⟩)
    rw [(C j).apply_symm_apply] at hval
    exact mem_iUnion.mpr ⟨j,hval ▸ (Hc j ((C j).symm ⟨x,hj⟩)).property⟩
  let f : U → X := fun x => g (r x)
  have hf : Continuous f :=
    (hg.comp hr.continuousOn (fun _ hx => hBK (hrmap hx))).domRestrict
  have hsource : (Subtype.val : U → E) '' D = U \ Ends := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨y.property,hy⟩
    · rintro ⟨hx,hq⟩; exact ⟨⟨x,hx⟩,hq,rfl⟩
  let source : D ≃ₜ (U \ Ends : Set E) :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage D).trans (Homeomorph.setCongr hsource)
  have hFV (x : g '' V) : F x ∈ V := by
    obtain ⟨y,hy,hyx⟩ := x.property
    rw [← hyx,hFg y (hVK hy)]
    exact hy
  let J : V ≃ₜ g '' V := {
    toFun := fun x => ⟨g x,mem_image_of_mem g x.property⟩
    invFun := fun x => ⟨F x,hFV x⟩
    left_inv := fun x => Subtype.ext (hFg x (hVK x.property))
    right_inv := fun x => Subtype.ext (by
      change g (F x) = x
      obtain ⟨y,hy,hyx⟩ := x.property
      rw [← hyx,hFg y (hVK hy)])
    continuous_toFun := (hg.mono hVK).domRestrict.subtype_mk _
    continuous_invFun := (hFc.comp continuous_subtype_val).subtype_mk _ }
  let H : D ≃ₜ g '' V := source.trans (Wraw.trans J)
  have hH (x : D) : f x = H x := congrArg g (hWraw (source x)).symm
  let q₀ : connectedComponentIn Ends (p : E) := ⟨p,mem_connectedComponentIn p.property⟩
  have hp : (p : E) ∈ K₀ \ g ⁻¹' ⋃ i,S i :=
    connectedComponentIn_nonempty_iff.mp
      ⟨r (Γ (q₀,⟨1/2,by norm_num⟩)),(hΓinto q₀ ⟨1/2,by norm_num⟩
        (by norm_num) (by norm_num)).2⟩
  have hgcut : MapsTo g (K₀ \ g ⁻¹' ⋃ i,S i) (R \ ⋃ i,S i) :=
    fun _ hx => ⟨hgR hx.1,hx.2⟩
  have hFcut : MapsTo F (R \ ⋃ i,S i) (K₀ \ g ⁻¹' ⋃ i,S i) := by
    intro x hx
    refine ⟨hFK hx.1,?_⟩
    change g (F x) ∉ ⋃ i,S i
    rw [hgF x hx.1]
    exact hx.2
  have hgcomp : MapsTo g (connectedComponentIn (K₀ \ g ⁻¹' ⋃ i,S i) (p : E))
      (connectedComponentIn (R \ ⋃ i,S i) (g p)) := by
    intro x hx
    exact connectedComponentIn_mono (g p) (image_subset_iff.mpr hgcut)
      ((hg.mono sdiff_subset).mapsTo_connectedComponentIn hp hx)
  have hFcomp : MapsTo F (connectedComponentIn (R \ ⋃ i,S i) (g p))
      (connectedComponentIn (K₀ \ g ⁻¹' ⋃ i,S i) (p : E)) := by
    intro x hx
    have hmem : F x ∈ connectedComponentIn (K₀ \ g ⁻¹' ⋃ i,S i) (F (g p)) :=
      connectedComponentIn_mono (F (g p)) (image_subset_iff.mpr hFcut)
      (hFc.continuousOn.mapsTo_connectedComponentIn (hgcut hp) hx)
    rwa [hFg p hp.1] at hmem
  have hphysicalcover : connectedComponentIn (R \ ⋃ i,S i) (g p) ⊆ g '' V := by
    intro x hx
    exact ⟨F x,hcover (hFcomp hx),hgF x (connectedComponentIn_subset _ _ hx).1⟩
  have hFi : InjOn F (⋃ i,S i) := by
    have hSR : (⋃ i,S i) ⊆ R := iUnion_subset (fun i => (hSO i).trans (hOR i))
    intro x hx y hy hxy
    exact (hgF x (hSR hx)).symm.trans ((congrArg g hxy).trans (hgF y (hSR hy)))
  apply exists_finitePL_prism_endpoint_sphere_of_core S sS hdis Hc C hC r hr hrv f hf
    (by intro j x; change g (r (C j x)) ∈ _ ↔ _; rw [hrv]; exact hcap j x)
    H hH O K W hO hOK hOR hSO hcenter (g p) hphysicalcover p Γ hΓzero
    (fun q t ht ht1 => ⟨(hΓinto q t ht ht1).1,hgcomp (hΓinto q t ht ht1).2⟩)
    F hF hFi (fun x => (hFg (r x) (hBK (hrmap x.property))).symm)

end PoincareConjecture.M76.PrismBelt
