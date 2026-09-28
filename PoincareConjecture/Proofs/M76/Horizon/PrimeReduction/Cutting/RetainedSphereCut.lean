import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalRawSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCutEndpointTransfer









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_retained_sphere_cut_with_original_collar
    {X ι κ : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R Q T U : Set X}
    (O : κ → Set X) (hQeq : Q = R \ ⋃ i,O i)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hQ : IsCompact Q) (he : PLDomain e Q)
    (sT : ChartwisePLSphere e T) (hTQ : T ⊆ interior Q)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ (Q' N : Set X) (B : Bool → Set X) (H : ∀ b,T ≃ₜ B b)
      (_sB : ∀ b,ChartwisePLSphere e (B b))
      (W : (T × unitInterval) ≃ₜ closure N) (r : X → X),
      Nonempty (OriginalFiniteSphereCollar e Q T N B) ∧
      (∀ (b : Bool) (A : Set X), ChartwisePLBall e A (B b) → A ⊆ Q' →
        ∃ A', Nonempty (ChartwisePLBall e A' T) ∧ A ⊆ interior A' ∧
          A' ⊆ A ∪ closure N ∧ A' ⊆ Q) ∧
      Q' = Q \ N ∧ Q' = R \ ((⋃ i,O i) ∪ N) ∧
      IsCompact Q' ∧ PLDomain e Q' ∧
      IsOpen N ∧ IsCompact (closure N) ∧ IsConnected (closure N) ∧
      closure N ⊆ U ∩ interior Q ∧
      (∀ i,Disjoint (closure N) (closure (O i))) ∧
      Pairwise (fun i j : Option κ =>
        Disjoint (closure (i.elim N O)) (closure (j.elim N O))) ∧
      closure N ∩ Q' = B false ∪ B true ∧
      Pairwise (fun b d => Disjoint (B b) (B d)) ∧
      frontier Q' = frontier Q ∪ ⋃ b,B b ∧ Q' \ U = Q \ U ∧
      (∀ x,(W (x,0) : X) = H false x ∧ (W (x,1) : X) = H true x) ∧
      (∀ x,(W (x,⟨(1 / 2 : ℝ),by norm_num⟩) : X) = x) ∧
      (∀ z,(W z : X) ∈ N ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ z,(W z : X) ∈ T ↔ (z.2 : ℝ) = 1 / 2) ∧ T ⊆ closure N ∧
      ContinuousOn r (Q \ T) ∧ MapsTo r (Q \ T) Q' ∧ EqOn r id Q' ∧
      (∀ x ∈ Q \ T,r x ∈ connectedComponentIn (Q \ T) x) ∧
      (∀ x ∈ Q',connectedComponentIn Q' x = connectedComponentIn (Q \ T) x ∩ Q') ∧
      ∀ x ∈ Q \ T,connectedComponentIn Q' (r x) =
        connectedComponentIn (Q \ T) x ∩ Q' := by
  obtain ⟨d, hdS, hdN, hraw, htransfer⟩ :=
    exists_marked_sphere_cut_with_original_collars (fun _ : Unit => T) (fun _ => sT)
      (fun _ _ hne => False.elim (hne (Subsingleton.elim _ _)))
      hQ he (fun _ => hTQ) hU (fun _ => hTU)
  have hmarks : ∃ (H : ∀ b : Unit × Bool, d.spheres b.1 ≃ₜ d.ports b)
      (W : ∀ i, (d.spheres i × unitInterval) ≃ₜ closure (d.collar i)),
      (∀ i x, (W i (x,0) : X) = H (i,false) x ∧ (W i (x,1) : X) = H (i,true) x) ∧
      (∀ i x, (W i (x,⟨(1/2 : ℝ),by norm_num⟩) : X) = x) ∧
      (∀ i z, (W i z : X) ∈ d.collar i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ i z, (W i z : X) ∈ d.spheres i ↔ (z.2 : ℝ) = 1/2) ∧
      (∀ i, d.spheres i ⊆ closure (d.collar i)) :=
    ⟨d.portMap, d.product, d.endpoints, d.center, d.openCoordinates,
      d.centerCoordinates, d.sphereClosure⟩
  rw [hdS] at hmarks
  obtain ⟨H, W, hW, hcenter, hopen, hT, hTN⟩ := hmarks
  let Q' := d.carrier
  let N := d.collar
  let B := d.ports
  have hcut : Q' = Q \ ⋃ i, N i := rfl
  have hQ' : IsCompact Q' := d.compactCut
  have he' : PLDomain e Q' := d.plCut
  have hN (i : Unit) : IsOpen (N i) ∧ IsCompact (closure (N i)) ∧
      IsConnected (closure (N i)) ∧ closure (N i) ⊆ U ∩ interior Q :=
    ⟨d.collarOpen i, (hdN i).1, (hdN i).2.1,
      fun x hx => ⟨(hdN i).2.2 hx, d.collarInterior i hx⟩⟩
  have hcontact := d.collarContact
  have hBdis := d.portDisjoint
  have hfront : frontier Q' = frontier Q ∪ ⋃ b, B b := d.frontierCut
  have hCR (i : Unit) : closure (N i) ⊆ Q := (d.collarInterior i).trans interior_subset
  obtain ⟨r, hrc, hrQ, hrfix, hrcc, hcomp, hrcomp⟩ :=
    exists_raw_sphere_cut_component_map Q Q' N (fun _ : Unit => T) W hcut
      hQ'.isClosed hCR d.collarDisjoint hopen hT hTN
  have hunit (A : Unit → Set X) : (⋃ i,A i) = A () := by
    ext x
    constructor
    · rintro ⟨_,⟨i,rfl⟩,hi⟩
      cases i
      exact hi
    · exact fun hx => mem_iUnion.mpr ⟨(),hx⟩
  have hcut' : Q' = Q \ N () := by simpa only [hunit] using hcut
  have htotal : Q' = R \ ((⋃ i,O i) ∪ N ()) := by
    rw [hcut',hQeq]
    ext x
    simp only [mem_sdiff,mem_union,not_or,and_assoc]
  have hcross (i : κ) : Disjoint (closure (N ())) (closure (O i)) := by
    have havoid : closure (O i) ⊆ (interior Q)ᶜ := by
      apply closure_minimal _ isOpen_interior.isClosed_compl
      intro x hx hxQ
      exact (hQeq.subset (interior_subset hxQ)).2 (mem_iUnion.mpr ⟨i,hx⟩)
    exact disjoint_left.mpr fun _ hx hn => havoid hn ((hN ()).2.2.2 hx).2
  have hcombined : Pairwise (fun i j : Option κ =>
      Disjoint (closure (i.elim (N ()) O)) (closure (j.elim (N ()) O))) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact hcross j
    | some i =>
      cases j with
      | none => exact (hcross i).symm
      | some j => exact hdis (fun h => hij (congrArg some h))
  have houtside : Q' \ U = Q \ U := by
    rw [hcut']
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1,hx.2⟩
    · intro hx
      exact ⟨⟨hx.1,fun hn => hx.2 ((hN ()).2.2.2 (subset_closure hn)).1⟩,hx.2⟩
  refine ⟨Q',N (),fun b => B ((),b),fun b => H ((),b),fun b => d.portPL ((),b),
    W (),r,hraw (), (fun b A => htransfer ((),b) A),hcut',htotal,hQ',he',
    (hN ()).1,(hN ()).2.1,(hN ()).2.2.1,
    (hN ()).2.2.2,hcross,hcombined,hcontact (),?_,?_,houtside,
    hW (),hcenter (),hopen (),hT (),hTN (),?_,?_,hrfix,?_,?_,?_⟩
  · intro b d hbd
    exact hBdis (fun h => hbd (congrArg Prod.snd h))
  · rw [hfront]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨⟨u,b⟩,hb⟩ := mem_iUnion.mp hx
      cases u
      exact mem_iUnion.mpr ⟨b,hb⟩
    · intro hx
      obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨((),b),hb⟩
  · simpa only [hunit] using hrc
  · simpa only [hunit] using hrQ
  · simpa only [hunit] using hrcc
  · simpa only [hunit] using hcomp
  · simpa only [hunit] using hrcomp

theorem exists_retained_sphere_cut_with_endpoint_transfer
    {X ι κ : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R Q T U : Set X}
    (O : κ → Set X) (hQeq : Q = R \ ⋃ i,O i)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hQ : IsCompact Q) (he : PLDomain e Q)
    (sT : ChartwisePLSphere e T) (hTQ : T ⊆ interior Q)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ (Q' N : Set X) (B : Bool → Set X) (H : ∀ b,T ≃ₜ B b)
      (_sB : ∀ b,ChartwisePLSphere e (B b))
      (W : (T × unitInterval) ≃ₜ closure N) (r : X → X),
      (∀ (b : Bool) (A : Set X), ChartwisePLBall e A (B b) → A ⊆ Q' →
        ∃ A', Nonempty (ChartwisePLBall e A' T) ∧ A ⊆ interior A' ∧
          A' ⊆ A ∪ closure N ∧ A' ⊆ Q) ∧
      Q' = Q \ N ∧ Q' = R \ ((⋃ i,O i) ∪ N) ∧
      IsCompact Q' ∧ PLDomain e Q' ∧
      IsOpen N ∧ IsCompact (closure N) ∧ IsConnected (closure N) ∧
      closure N ⊆ U ∩ interior Q ∧
      (∀ i,Disjoint (closure N) (closure (O i))) ∧
      Pairwise (fun i j : Option κ =>
        Disjoint (closure (i.elim N O)) (closure (j.elim N O))) ∧
      closure N ∩ Q' = B false ∪ B true ∧
      Pairwise (fun b d => Disjoint (B b) (B d)) ∧
      frontier Q' = frontier Q ∪ ⋃ b,B b ∧ Q' \ U = Q \ U ∧
      (∀ x,(W (x,0) : X) = H false x ∧ (W (x,1) : X) = H true x) ∧
      (∀ x,(W (x,⟨(1 / 2 : ℝ),by norm_num⟩) : X) = x) ∧
      (∀ z,(W z : X) ∈ N ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ z,(W z : X) ∈ T ↔ (z.2 : ℝ) = 1 / 2) ∧ T ⊆ closure N ∧
      ContinuousOn r (Q \ T) ∧ MapsTo r (Q \ T) Q' ∧ EqOn r id Q' ∧
      (∀ x ∈ Q \ T,r x ∈ connectedComponentIn (Q \ T) x) ∧
      (∀ x ∈ Q',connectedComponentIn Q' x = connectedComponentIn (Q \ T) x ∩ Q') ∧
      ∀ x ∈ Q \ T,connectedComponentIn Q' (r x) =
        connectedComponentIn (Q \ T) x ∩ Q' := by
  obtain ⟨Q', N, B, H, sB, W, r, _, h⟩ :=
    exists_retained_sphere_cut_with_original_collar O hQeq hdis hQ he sT hTQ hU hTU
  exact ⟨Q', N, B, H, sB, W, r, h⟩

theorem exists_retained_sphere_cut
    {X ι κ : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R Q T U : Set X}
    (O : κ → Set X) (hQeq : Q = R \ ⋃ i,O i)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hQ : IsCompact Q) (he : PLDomain e Q)
    (sT : ChartwisePLSphere e T) (hTQ : T ⊆ interior Q)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ (Q' N : Set X) (B : Bool → Set X) (H : ∀ b,T ≃ₜ B b)
      (_sB : ∀ b,ChartwisePLSphere e (B b))
      (W : (T × unitInterval) ≃ₜ closure N) (r : X → X),
      Q' = Q \ N ∧ Q' = R \ ((⋃ i,O i) ∪ N) ∧
      IsCompact Q' ∧ PLDomain e Q' ∧
      IsOpen N ∧ IsCompact (closure N) ∧ IsConnected (closure N) ∧
      closure N ⊆ U ∩ interior Q ∧
      (∀ i,Disjoint (closure N) (closure (O i))) ∧
      Pairwise (fun i j : Option κ =>
        Disjoint (closure (i.elim N O)) (closure (j.elim N O))) ∧
      closure N ∩ Q' = B false ∪ B true ∧
      Pairwise (fun b d => Disjoint (B b) (B d)) ∧
      frontier Q' = frontier Q ∪ ⋃ b,B b ∧ Q' \ U = Q \ U ∧
      (∀ x,(W (x,0) : X) = H false x ∧ (W (x,1) : X) = H true x) ∧
      (∀ x,(W (x,⟨(1 / 2 : ℝ),by norm_num⟩) : X) = x) ∧
      (∀ z,(W z : X) ∈ N ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ z,(W z : X) ∈ T ↔ (z.2 : ℝ) = 1 / 2) ∧ T ⊆ closure N ∧
      ContinuousOn r (Q \ T) ∧ MapsTo r (Q \ T) Q' ∧ EqOn r id Q' ∧
      (∀ x ∈ Q \ T,r x ∈ connectedComponentIn (Q \ T) x) ∧
      (∀ x ∈ Q',connectedComponentIn Q' x = connectedComponentIn (Q \ T) x ∩ Q') ∧
      ∀ x ∈ Q \ T,connectedComponentIn Q' (r x) =
        connectedComponentIn (Q \ T) x ∩ Q' := by
  obtain ⟨Q', N, B, H, sB, W, r, _, h⟩ :=
    exists_retained_sphere_cut_with_endpoint_transfer O hQeq hdis hQ he sT hTQ hU hTU
  exact ⟨Q', N, B, H, sB, W, r, h⟩

end PoincareConjecture.M76
