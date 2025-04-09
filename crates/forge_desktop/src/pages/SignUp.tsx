import { SignUp } from "@clerk/clerk-react";
import { CardContent } from "../components/ui/card";

export function SignUpPage() {
    return (
        <div className="min-h-screen w-full flex items-center justify-center bg-background">
            <CardContent>
                <SignUp
                    routing="path"
                    path="/sign-up"
                    signInUrl="/sign-in"
                    forceRedirectUrl="/"
                />
            </CardContent>
        </div>
    );
} 