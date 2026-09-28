import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FamilyCocoreSection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocorePositionedProduct

set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem exists_sphere_family_cocore_positioned_product_at_height
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (s : ∀i,ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀x,∃i,x∈(e i).source) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space⊆Q.target)
    (hJcv : Convex ℝ J.space) (H : V3 ≃ᴬ[ℝ] P3) (t : ℝ)
    (hpres : HasDisjointPolygonPresentation
      ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t}))
    (hinside : ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})⊆interior J.space)
    (hcross : ∀w∈(Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t},
      ∀O : Set V3,IsOpen O → w∈O →
        ∃B : OpenPartialHomeomorph V3 P3,
          w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
          LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀x∈B.source,Q.symm x∈⋃i,S i ↔ (B x).2=0) ∧
          ∀x∈B.source,(H x).2-t=(B x).1.1)
    (hne : ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t}).Nonempty) :
    ∃(i : κ) (n : ℕ) (L : Polygon V3 (n+3)) (rho : V2 × ℝ → X),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      L.boundary ℝ⊆(Q '' (S i∩Q.source)∩interior J.space)∩{x | (H x).2=t} ∧
      IsCompact (((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})\L.boundary ℝ) ∧
      PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) (Q.symm '' interior J.space) ∧
      (∀z∈Disk ×ˢ Icc (-1 : ℝ) 1,rho z∈S i ↔ z.1∈Rim) ∧
      (∀j,j≠i → Disjoint (rho '' (Disk ×ˢ Icc (-1 : ℝ) 1)) (S j)) ∧
      (∀c : Bool,Disjoint (rho '' (Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)}))
        (Q.symm '' (Q.target∩{x | (H x).2=t}))) ∧
      (rho '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2)))∩
        (Q.symm '' (Q.target∩{x | (H x).2=t}))=Q.symm '' L.boundary ℝ := by
  obtain ⟨i,n,L,D,U,hLi,hL,hD,hDsub,_,hcontact,hrem,hU,hDU,hUJ,hother,hisolate,hcharts⟩ :=
    exists_sphere_family_cocore_innermost_disk_at_height S s hdis Q J hJQ hJcv H t
      hpres hinside hcross hne
  obtain ⟨rho,hρ,hρi,hρU,hρS,hcap,hstrip⟩ :=
    (s i).exists_cocore_positioned_product_of_disk hcover Q hQ J hJ hJQ H t
      L hLi hL hD hDsub hcontact hU hDU hUJ hisolate hcharts
  have hLS : L.boundary ℝ⊆(Q '' (S i∩Q.source)∩interior J.space)∩{x | (H x).2=t} :=
    fun x hx => ⟨⟨(hcontact.symm.subset hx).2,(hDsub (hD.1 hx)).1⟩,(hDsub (hD.1 hx)).2⟩
  refine ⟨i,n,L,rho,hLi,hL,hLS,hrem,hρ,hρi,
    (fun z hz => image_mono hUJ (hρU hz)),hρS,?_,hcap,hstrip⟩
  intro j hji
  apply (hother j hji).mono_left
  rintro _ ⟨z,hz,rfl⟩
  exact hρU hz

theorem exists_sphere_family_cocore_positioned_product
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (s : ∀i,ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀x,∃i,x∈(e i).source) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space⊆Q.target)
    (hJcv : Convex ℝ J.space) (H : V3 ≃ᴬ[ℝ] P3) {a b : ℝ} (hab : a<b)
    (hband : ∀x∈Q '' ((⋃i,S i)∩Q.source)∩J.space,(H x).2∈Ioo a b → x∈interior J.space) :
    ∃t∈Ioo a b,
      HasDisjointPolygonPresentation ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t}) ∧
      (((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t}=∅) ∨
        ∃(i : κ) (n : ℕ) (L : Polygon V3 (n+3)) (rho : V2 × ℝ → X),
          Function.Injective L ∧ L.HasSimplicialEdges ∧
          L.boundary ℝ⊆(Q '' (S i∩Q.source)∩interior J.space)∩{x | (H x).2=t} ∧
          IsCompact (((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})\L.boundary ℝ) ∧
          PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
          InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
          MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) (Q.symm '' interior J.space) ∧
          (∀z∈Disk ×ˢ Icc (-1 : ℝ) 1,rho z∈S i ↔ z.1∈Rim) ∧
          (∀j,j≠i → Disjoint (rho '' (Disk ×ˢ Icc (-1 : ℝ) 1)) (S j)) ∧
          (∀c : Bool,Disjoint (rho '' (Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)}))
            (Q.symm '' (Q.target∩{x | (H x).2=t}))) ∧
          (rho '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2)))∩
            (Q.symm '' (Q.target∩{x | (H x).2=t}))=Q.symm '' L.boundary ℝ) := by
  let A : V3 →ᵃ[ℝ] ℝ :=
    ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap).toAffineMap
  obtain ⟨t,ht,_,hpres,hcross⟩ :=
    exists_sphere_family_regular_cocore_section S s hdis Q hQ J hJ hJQ A hab hband
  refine ⟨t,ht,hpres,?_⟩
  by_cases hempty : ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})=∅
  · exact Or.inl hempty
  · exact Or.inr (exists_sphere_family_cocore_positioned_product_at_height S s hdis hcover Q hQ
      J hJ hJQ hJcv H t hpres (fun x hx => hband x hx.1 (hx.2 ▸ ht)) hcross
      (Set.nonempty_iff_ne_empty.mpr hempty))

end PoincareConjecture.M76
