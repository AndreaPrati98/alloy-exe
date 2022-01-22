sig Author{}
sig Location{}
sig PackagingTechnology{}

sig SoftwareModule{
    author: Author,
    packaging: PackagingTechnology
}

sig Device{
    location: Location,
    packagingHandled: set PackagingTechnology,
    hostedModules: set SoftwareModule
}

sig Configuration{
    devices: set Device,
    canHost: set SoftwareModule
}

fact f1{
    all c:Configuration | c.canHost = packaging.(c.devices.packagingHandled) 
}

fact device{
    no d:Device | (d.hostedModules.packaging & d.packagingHandled )!= d.hostedModules.packaging
}

fact noReplica{
    all d:Device, sm:SoftwareModule | sm in d.hostedModules implies #(d.hostedModules & sm) = 1
}

fun a[c:Configuration,sm:SoftwareModule]: set Device{
    c.devices & hostedModules.sm
}

pred deploy[c,c_up:Configuration,sm:SoftwareModule, d,d_up:Device]{
    d in c.devices
    not (sm in d.hostedModules)
    not (sm in c.canHost)
    sm.packaging in d.packagingHandled

    //POST
    d_up.location = d.location
    d_up.packagingHandled = d.packagingHandled
    d_up.hostedModules = d.hostedModules + sm
    
    c_up.devices = c.devices - d + d_up
    c_up.canHost = c.canHost + sm
}