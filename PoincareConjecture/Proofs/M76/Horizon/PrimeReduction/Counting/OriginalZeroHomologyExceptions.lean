import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalCoordinateCutHomology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ClosedAttachmentComponentCarriers



set_option autoImplicit false
open Set CategoryTheory Limits
namespace PoincareConjecture.M76
universe u v

theorem ncard_zero_cut_components_le_original_exceptions
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    {κ : Type v} [Finite κ] {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
    {K : Set E} {R Q : Set X} (g : E → X) (hg : ContinuousOn g K)
    (hgR : MapsTo g K R) (F : X → E) (hFK : MapsTo F R K)
    (hgF : ∀ y ∈ R, g (F y) = y)
    (O S : κ → Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃ i,O i) (hcQ : IsClosed Q)
    (hCR : ∀ i,closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hO : ∀ i z,(W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS : ∀ i z,(W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSO : ∀ i,S i ⊆ O i)
    (bad : Set (ConnectedComponents (K \ g ⁻¹' ⋃ i,S i : Set E))) (hbad : bad.Finite)
    (M : ModuleCat.{u} (ZMod 2))
    (hgood : ∀ (x : Q) (hxF : F x ∈ K \ g ⁻¹' ⋃ i,S i),
      ConnectedComponents.mk (⟨F x,hxF⟩ : (K \ g ⁻¹' ⋃ i,S i : Set E)) ∉ bad →
      ¬ IsZero ((TopCat.toSSet.obj (TopCat.of (connectedComponentIn Q (x : X)))).homology M 1))
    (D : ConnectedComponents Q → Set X)
    (hD : ∀ x : Q, D (ConnectedComponents.mk x) = connectedComponentIn Q (x : X)) :
    {c | IsZero ((TopCat.toSSet.obj (TopCat.of (D c))).homology M 1)}.ncard ≤ bad.ncard := by
  classical
  obtain ⟨_,_,_,_,_,hcomp,_⟩ := exists_raw_sphere_cut_component_map R Q O S W hQ hcQ
    hCR hdis hO hS (fun i => (hSO i).trans subset_closure)
  have hQR : Q ⊆ R := hQ ▸ sdiff_subset
  have hQraw : Q ⊆ R \ ⋃ i,S i := by
    intro x hx
    exact ⟨hQR hx,fun hs => (hQ.subset hx).2 (iUnion_mono hSO hs)⟩
  have hFraw (x : Q) : F x ∈ K \ g ⁻¹' ⋃ i,S i := by
    refine ⟨hFK (hQR x.property),?_⟩
    simpa only [mem_preimage,hgF x (hQR x.property)] using (hQraw x.property).2
  let point (c : ConnectedComponents Q) : Q := (ConnectedComponents.surjective_coe c).choose
  have hpoint (c) : ConnectedComponents.mk (point c) = c :=
    (ConnectedComponents.surjective_coe c).choose_spec
  let label (c : ConnectedComponents Q) :=
    ConnectedComponents.mk (⟨F (point c),hFraw (point c)⟩ : (K \ g ⁻¹' ⋃ i,S i : Set E))
  have hinj : Function.Injective label := by
    intro c d hcd
    have hraw : F (point d) ∈ connectedComponentIn (K \ g ⁻¹' ⋃ i,S i) (F (point c)) :=
      (Topology.mem_componentIn_iff_component_class (hFraw (point c)) (hFraw (point d))).mpr hcd.symm
    have hmaps : MapsTo g (K \ g ⁻¹' ⋃ i,S i) (R \ ⋃ i,S i) := fun y hy => ⟨hgR hy.1,hy.2⟩
    have hphysical := connectedComponentIn_mono _ (mapsTo_iff_image_subset.mp hmaps)
      ((hg.mono sdiff_subset).mapsTo_connectedComponentIn (hFraw (point c)) hraw)
    have hphysical' : (point d : X) ∈ connectedComponentIn (R \ ⋃ i,S i) (point c : X) := by
      simpa only [hgF _ (hQR (point c).property),hgF _ (hQR (point d).property)] using hphysical
    have hcut : (point d : X) ∈ connectedComponentIn Q (point c : X) :=
      (hcomp _ (point c).property).symm.subset ⟨hphysical',(point d).property⟩
    have he := (Topology.mem_componentIn_iff_component_class (point c).property (point d).property).mp hcut
    simpa only [hpoint] using he.symm
  apply ncard_le_ncard_of_injOn label _ hinj.injOn hbad
  intro c hc
  by_contra hcbad
  apply hgood (point c) (hFraw (point c)) hcbad
  have he := hD (point c)
  rw [hpoint] at he
  exact he ▸ hc

end PoincareConjecture.M76
