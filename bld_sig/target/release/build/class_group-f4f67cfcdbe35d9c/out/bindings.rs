/* automatically generated by rust-bindgen */

pub type __darwin_size_t = ::std::os::raw::c_ulong;
pub type pari_ulong = ::std::os::raw::c_ulong;
pub type GEN = *mut ::std::os::raw::c_long;
extern "C" {
    pub fn nupow(x: GEN, n: GEN, L: GEN) -> GEN;
}
extern "C" {
    pub fn primeform(x: GEN, p: GEN, prec: ::std::os::raw::c_long) -> GEN;
}
extern "C" {
    pub fn qfbcompraw(x: GEN, y: GEN) -> GEN;
}
extern "C" {
    pub fn qfi(x: GEN, y: GEN, z: GEN) -> GEN;
}
extern "C" {
    pub fn GENtostr(x: GEN) -> *mut ::std::os::raw::c_char;
}
extern "C" {
    pub fn gadd(x: GEN, y: GEN) -> GEN;
}
extern "C" {
    pub fn gneg(x: GEN) -> GEN;
}
extern "C" {
    pub fn compo(x: GEN, n: ::std::os::raw::c_long) -> GEN;
}
extern "C" {
    pub fn mkintn(n: ::std::os::raw::c_long, ...) -> GEN;
}
extern "C" {
    pub fn pari_init(parisize: usize, maxprime: pari_ulong);
}
extern "C" {
    pub fn shifti(x: GEN, n: ::std::os::raw::c_long) -> GEN;
}
extern "C" {
    pub fn isprime(x: GEN) -> ::std::os::raw::c_long;
}
