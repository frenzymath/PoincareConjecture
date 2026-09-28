import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.RectangleCapPages
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.RectangleCutDiskContacts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.SphereDiskContactSeparation

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem same_face_rectangles_disjoint_in_cut_ball
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [Finite ι] [DecidableEq ι]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    (cut rim : ι → Set E) (hcut : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (cut i) (rim i))
    (hsub : ∀ i, cut i ⊆ convexHull ℝ (t : Set E))
    (hrim : ∀ i, cut i ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim i)
    (hdis : Pairwise fun i j => Disjoint (cut i) (cut j))
    (hphysical : g '' (⋃ i, cut i) = S ∩ (g '' convexHull ℝ (t : Set E)))
    {B R : Set E} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B R)
    (hR : R = B ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ ⋃ i, cut i))
    (hwhole : ∀ i, (B ∩ cut i).Nonempty → cut i ⊆ R)
    (f : TetrahedronFace K t) {k l : (D f).Region}
    (hk : (D f).carrier k ⊆ B) (hl : (D f).carrier l ⊆ B) (hkl : k ≠ l) :
    Disjoint ((D f).carrier k) ((D f).carrier l) := by
  classical
  obtain ⟨owner,howner,_,_,_⟩ := exists_original_rectangle_cut_disk_contacts K g hgi ht ht4
    D cut rim hcut hsub hrim hdis hphysical
  have hfacet : convexHull ℝ (f.1.1 : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
    apply (K.indep ht).convexHull_subset_intrinsicFrontier
    exact Finset.ssubset_iff_subset_ne.mpr ⟨f.2,fun he => by
      have hc := congrArg Finset.card he
      rw [f.1.2.2,ht4] at hc
      omega⟩
  have hMF (m : (D f).Region) : (D f).carrier m ⊆
      intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) :=
    ((D f).carrier_subset_face m).trans hfacet
  have hMR (m : (D f).Region) (hm : (D f).carrier m ⊆ B) : (D f).carrier m ⊆ R :=
    fun x hx => hR.symm.subset ⟨hm hx,Or.inl (hMF m hx)⟩
  have hinter : (D f).carrier k ∩ (D f).carrier l ⊆ ⋃ i, (D f).arc i := by
    intro x hx
    by_contra hxc
    have he := ((D f).componentClosure k x ⟨hx.1,hxc⟩).2.symm.trans
      ((D f).componentClosure l x ⟨hx.2,hxc⟩).2
    exact hkl ((D f).carrierInjective he)
  refine disjoint_left.mpr ?_
  intro x hxk hxl
  have hxcut := hinter ⟨hxk,hxl⟩
  have hkcap : ∃ b : Bool, x ∈ (D f).arc ((D f).cap k b) := by
    rcases ((D f).cutContact k).subset ⟨hxk,hxcut⟩ with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have hlcap : ∃ b : Bool, x ∈ (D f).arc ((D f).cap l b) := by
    rcases ((D f).cutContact l).subset ⟨hxl,hxcut⟩ with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨b,hxb⟩ := hkcap
  obtain ⟨c,hxc⟩ := hlcap
  have hsame : (D f).cap k b = (D f).cap l c := by
    by_contra hne
    exact disjoint_left.mp ((D f).arcDisjoint hne) hxb hxc
  let j := (D f).cap k b
  obtain ⟨N,n,hN,hNM,hWn,hNcut⟩ := (D f).exists_cap_page k b
  obtain ⟨P,p,hP,hPM,hWp,hPcut⟩ := (D f).exists_cap_page l c
  have hNP : N ∩ P = (D f).arc j := by
    apply Subset.antisymm
    · intro y hy
      exact hNcut.subset ⟨hy.1,hinter ⟨hNM hy.1,hPM hy.2⟩⟩
    · intro y hy
      exact ⟨hN.1 (hWn hy),hP.1 (hWp (hsame ▸ hy))⟩
  have hCsub : (D f).arc j ⊆ cut (owner f j) := (howner f j).trans (hcut _).1
  have hCR : cut (owner f j) ⊆ R := hwhole _ ⟨x,hk hxk,hCsub hxb⟩
  obtain ⟨a,z,haz,hr⟩ := ((D f).arcBall j).exists_boundary_eq_pair
  have hW : IsFinitePLBallPair ℝ ((D f).arc j) {a,z} := hr ▸ (D f).arcBall j
  apply not_three_boundary_disk_pages hB (by simp) hN hP (hcut (owner f j)) hW haz
    hWn (fun y hy => hWp (hsame ▸ hy)) hNP
    (hNM.trans (hMR k hk)) (hPM.trans (hMR l hl)) hCR ?_ hCsub
  rintro y ⟨hyN | hyP,hyC⟩
  · exact (hrim _).subset ⟨hyC,hMF k (hNM hyN)⟩
  · exact (hrim _).subset ⟨hyC,hMF l (hPM hyP)⟩

end PoincareConjecture.M76.PrismBelt
