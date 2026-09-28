import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalSeparatedRepairedDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalRetainedDiskSides

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "Source" => SProd.sprod Disk (Icc (-1 : ℝ) 1)
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_original_circle_repaired_disk_transport
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {T : Set E} (hTK : T ⊆ K.space)
    (hP : MapsTo P.map Source (interior (g '' T))) (hS : S ⊆ g '' K.space)
    (v : Fin 2 → Set V3) {r₀ : Set V3}
    (hv : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (v b) r₀)
    (hwhole : v 0 ∪ v 1 = Sphere) (hinter : v 0 ∩ v 1 = r₀)
    (hband : P.map '' (Rim ×ˢ J) ⊆ S)
    (hcenter : P.map '' (Rim ×ˢ {(0 : ℝ)}) = s.map '' r₀)
    (hopen : IsOpen ((Subtype.val : S → X) ⁻¹'
      (P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)))))
    (k q : Bool → Set V3)
    (hk : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (k b) (q b) ∧ k b ⊆ Sphere ∧
      s.map '' q b = P.capRimSet b ∧ (s.map '' k b) ∩ P.closedStrip = s.map '' q b)
    (hcover : ((s.map '' k true) ∪ (s.map '' k false)) ∪
      (P.map '' (Rim ×ˢ J)) = S) :
    ∃ side : Bool → Fin 2, side false ≠ side true ∧
      ∀ b : Bool,
        let raw := (s.map '' v (side b)) ∪ (j '' Disk)
        let separated := (s.map '' k b) ∪ P.capDisk b
        let A := K.space ∩ g ⁻¹' raw
        let B := K.space ∩ g ⁻¹' separated
        g '' A = raw ∧ g '' B = separated ∧
          ∃ h : E → E, FinitePiecewiseAffineOn h A ∧ InjOn h A ∧ h '' A = B ∧
            EqOn h id (K.space ∩ g ⁻¹' (s.map '' k b)) ∧
            EqOn h id (A \ g ⁻¹' interior (g '' T)) ∧
            (∀ x ∈ A, h x ∈ T ↔ x ∈ T) ∧
            (∃ G : (A ∩ T : Set E) ≃ₜ (B ∩ T : Set E),
              ∀ x : (A ∩ T : Set E), (G x : E) = h x) ∧
            ∀ (Z r : Set E), IsFinitePLBallPair (ℝ × ℝ) Z r → Z ⊆ A → Z ⊆ T →
              Disjoint (g '' r) (interior (g '' T)) →
              IsFinitePLBallPair (ℝ × ℝ) (h '' Z) r ∧ EqOn h id r ∧ h '' Z ⊆ T ∧
                (h '' Z) \ g ⁻¹' interior (g '' T) = Z \ g ⁻¹' interior (g '' T) ∧
                ((∀ x ∈ g '' Z, connectedComponentIn (raw ∩ (g '' T)) x = g '' Z) →
                  ∀ x ∈ g '' (h '' Z),
                    connectedComponentIn (separated ∩ (g '' T)) x = g '' (h '' Z)) := by
  obtain ⟨side,hside,hparts⟩ := P.original_retained_disk_side_decomposition s v hv hwhole
    hinter hband hcenter hopen k q hk hcover
  obtain ⟨f,hf,hfi,hfK,hfg,hcarrier,htransport⟩ :=
    P.exists_original_separated_repaired_disk_transport s he K hK hg hgi hTK hP hS k q hk
  refine ⟨side,hside,?_⟩
  intro b
  let D := K.space ∩ g ⁻¹' (s.map '' k b)
  let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
  let t := if b then (1/2 : ℝ) else -(1/2)
  let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
  let N := Disk ×ˢ {t}
  let A := D ∪ f '' C
  let B := D ∪ f '' N
  have hCsub : C ⊆ Source := by
    rintro ⟨x,u⟩ (⟨hx,hu⟩ | ⟨hx,hu⟩)
    · exact ⟨hx,by rw [show u = 0 from hu]; norm_num⟩
    · refine ⟨sphere_subset_closedBall hx,?_⟩
      cases b <;> dsimp [I] at hu <;> constructor <;> linarith [hu.1,hu.2]
  have hNsub : N ⊆ Source := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    refine ⟨hx,?_⟩
    rw [show u = t from hu]
    cases b <;> norm_num [t]
  have hDimage : g '' D = s.map '' k b := by
    rw [image_inter_preimage]
    apply inter_eq_right.mpr
    rintro _ ⟨x,hx,rfl⟩
    apply hS
    rw [s.map_eq ⟨x,(hk b).2.1 hx⟩]
    exact (s.parametrization ⟨x,(hk b).2.1 hx⟩).property
  have hfgimage (U : Set (V2 × ℝ)) (hU : U ⊆ Source) :
      g '' (f '' U) = P.map '' U := by
    rw [←image_comp]
    exact image_congr (fun x hx => hfg x (hU hx))
  obtain ⟨_,_,_,hcup,_,_,_,_⟩ := P.exists_original_product_cap_replacement b
  have hAimage : g '' A = (s.map '' v (side b)) ∪ (j '' Disk) := by
    rw [image_union,hDimage,hfgimage C hCsub,hcup,(hparts b).2]
    ac_rfl
  have hBimage : g '' B = (s.map '' k b) ∪ P.capDisk b := by
    rw [image_union,hDimage,hfgimage N hNsub]
    rfl
  have hAK : A ⊆ K.space := union_subset inter_subset_left (by
    rintro _ ⟨z,hz,rfl⟩
    exact hfK (hCsub hz))
  have hBK : B ⊆ K.space := union_subset inter_subset_left (by
    rintro _ ⟨z,hz,rfl⟩
    exact hfK (hNsub hz))
  have hpre (U : Set E) (hUK : U ⊆ K.space) : K.space ∩ g ⁻¹' (g '' U) = U := by
    apply Subset.antisymm
    · rintro x ⟨hx,y,hy,hyx⟩
      exact (hgi (hUK hy) hx hyx) ▸ hy
    · exact fun x hx => ⟨hUK hx,mem_image_of_mem g hx⟩
  have hAeq : K.space ∩ g ⁻¹' ((s.map '' v (side b)) ∪ (j '' Disk)) = A := by
    rw [←hAimage]
    exact hpre A hAK
  have hBeq : K.space ∩ g ⁻¹' ((s.map '' k b) ∪ P.capDisk b) = B := by
    rw [←hBimage]
    exact hpre B hBK
  dsimp only
  rw [hAeq,hBeq]
  refine ⟨hAimage,hBimage,?_⟩
  obtain ⟨h,hh,hhi,hAB,hfix,hsupport,hpres,hsection,hdisk⟩ := htransport b
  refine ⟨h,hh,hhi,hAB,hfix,hsupport,hpres,hsection,?_⟩
  intro Z r hZ hZA hZT hr
  have hout := hdisk Z r hZ hZA hZT hr
  dsimp only [A,B,C,N,D,I,t] at hAimage hBimage
  simpa only [hAimage,hBimage] using hout

end PoincareConjecture.M76.OriginalDiskProduct
