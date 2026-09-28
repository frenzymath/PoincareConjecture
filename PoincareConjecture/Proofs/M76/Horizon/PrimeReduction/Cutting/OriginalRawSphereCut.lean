import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RawSphereCutComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalSphereCutComponents









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_original_cut_with_raw_components
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (Q : Set X) (B : κ × Bool → Set X) (H : ∀ b, S b.1 ≃ₜ B b)
      (_sB : ∀ b, ChartwisePLSphere e (B b)) (O : κ → Set X)
      (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i)) (r : X → X),
      Q = R \ ⋃ i, O i ∧ IsCompact Q ∧ PLDomain e Q ∧
      (∀ i, IsOpen (O i) ∧ IsCompact (closure (O i)) ∧
        IsConnected (closure (O i)) ∧ closure (O i) ⊆ U ∩ interior R) ∧
      Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) ∧
      (∀ i, closure (O i) ∩ Q = B (i,false) ∪ B (i,true)) ∧
      Pairwise (fun b d => Disjoint (B b) (B d)) ∧
      frontier Q = frontier R ∪ ⋃ b, B b ∧
      (∀ i x, (W i (x,0) : X) = H (i,false) x ∧
        (W i (x,1) : X) = H (i,true) x) ∧
      (∀ i x, (W i (x,⟨(1 / 2 : ℝ),by norm_num⟩) : X) = x) ∧
      (∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1 / 2) ∧
      (∀ i, S i ⊆ closure (O i)) ∧
      ContinuousOn r (R \ ⋃ i, S i) ∧ MapsTo r (R \ ⋃ i, S i) Q ∧ EqOn r id Q ∧
      (∀ x ∈ R \ ⋃ i, S i, r x ∈ connectedComponentIn (R \ ⋃ i, S i) x) ∧
      (∀ x ∈ Q, connectedComponentIn Q x = connectedComponentIn (R \ ⋃ i, S i) x ∩ Q) ∧
      ∀ x ∈ R \ ⋃ i, S i,
        connectedComponentIn Q (r x) = connectedComponentIn (R \ ⋃ i, S i) x ∩ Q := by
  obtain ⟨Q,B,H,sB,O,_,_,_,hQeq,hQ,hQPL,hO,hCC,hinc,_,_,hBB,
    _,_,_,_,_,_,_,W,hW,hcenter⟩ :=
    exists_original_sphere_cut_components S sS hdis hR he hSR hU hSU
  have hCR (i : κ) : closure (O i) ⊆ R :=
    (hO i).2.2.2.trans (inter_subset_right.trans interior_subset)
  have hOi := marked_cut_collar_open_iff R Q O B W (fun i b => H (i,b))
    hQeq hCR hCC hinc hW
  have hSi (i : κ) (z : S i × unitInterval) :
      (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1 / 2 := by
    have hh := mem_collar_endpoint_iff (W i) (Homeomorph.refl (S i))
      ⟨(1 / 2 : ℝ),by norm_num⟩ (hcenter i) z
    exact hh.trans Subtype.ext_iff
  have hSC (i : κ) : S i ⊆ closure (O i) := by
    intro x hx
    have hh := (W i (⟨x,hx⟩,⟨(1 / 2 : ℝ),by norm_num⟩)).property
    simpa only [hcenter] using hh
  obtain ⟨_,_,hQf,hif,_⟩ := finite_collar_cut_geometry hR
    (fun i => (hO i).1) (fun i => (hO i).2.2.2.trans inter_subset_right) hCC
  rw [←hQeq] at hQf hif
  have hfront : frontier Q = frontier R ∪ ⋃ b, B b := by
    rw [hQf]
    congr 1
    have hf (i : κ) : frontier (O i) = B (i,false) ∪ B (i,true) :=
      (hif i).symm.trans (hinc i)
    ext x
    simp only [hf,mem_iUnion,mem_union]
    constructor
    · rintro ⟨i,hi | hi⟩
      · exact ⟨(i,false),hi⟩
      · exact ⟨(i,true),hi⟩
    · rintro ⟨⟨i,b⟩,hi⟩
      refine ⟨i,?_⟩
      cases b
      · exact Or.inl hi
      · exact Or.inr hi
  obtain ⟨r,hrc,hrQ,hrfix,hrcc,hcomp,hrcomp⟩ := exists_raw_sphere_cut_component_map
    R Q O S W hQeq hQ.isClosed hCR hCC hOi hSi hSC
  exact ⟨Q,B,H,sB,O,W,r,hQeq,hQ,hQPL,hO,hCC,hinc,hBB,hfront,hW,hcenter,
    hOi,hSi,hSC,hrc,hrQ,hrfix,hrcc,hcomp,hrcomp⟩

end PoincareConjecture.M76
