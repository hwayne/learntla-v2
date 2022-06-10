$failstr = "Error: Invariant Invariant is violated."
$a = ,1
$b = ,-1
$a.Clear()
$b.Clear()

for($i=400; $i -lt 1000; $i++)
{ 
    tlacli check .\calculator__3.tla --const NumInputs 5 --const Target $i --inv Invariant | Select-String $failstr -Quiet -OutVariable found
    if($found) {$a += $i}
    else {$b += $i}

}

echo $a
echo $b