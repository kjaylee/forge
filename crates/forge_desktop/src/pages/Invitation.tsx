import { useAuth, useUser } from "@clerk/clerk-react";
import { Navigate } from "react-router-dom";
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Loader2, Sparkles } from "lucide-react";
import { useOnboarding } from "@/hooks/useOnboarding";
import { useInviteCode } from "@/hooks/useInviteCode";
import { Input } from "@/components/ui/input";
import { LoadingScreen } from "@/components/LoadingScreen";
import { UserButton } from "@/components/UserButton";

export function InvitationPage() {
    const { isLoaded: isAuthLoaded, isSignedIn } = useAuth();
    const { user } = useUser();
    const { isLoading: isCheckingStatus, isWaitlisted, error } = useOnboarding();
    const { value, onChange, onSubmit, error: inviteError, isLoading, isRedeemed } = useInviteCode();
    const isDisabled = !value.trim() || isLoading;

    if (!isAuthLoaded || isCheckingStatus) {
        return <LoadingScreen />;
    }

    if (!isSignedIn) {
        return <Navigate to="/sign-in" replace />;
    }

    if (error) {
        return (
            <div className="min-h-screen w-full flex items-center justify-center bg-gradient-to-b from-background to-background/80">
                <Card className="w-full max-w-md border-destructive/20">
                    <CardHeader>
                        <CardTitle className="text-destructive">Error</CardTitle>
                        <CardDescription>
                            Failed to check access status. Please try again later.
                        </CardDescription>
                    </CardHeader>
                </Card>
            </div>
        );
    }

    // Redirect to main app if user is not waitlisted
    if (!isWaitlisted || isRedeemed) {
        return <Navigate to="/" replace />;
    }

    return (
        <div className="min-h-screen w-full flex flex-col bg-gradient-to-b from-background to-background/80">
            <div className="flex justify-end p-4 border-b border-border/50 bg-card/50 backdrop-blur-sm">
                <UserButton />
            </div>
            <div className="flex-1 flex items-center justify-center p-4">
                <div className="w-full max-w-md">
                    <Card className="backdrop-blur-sm border-primary/10 shadow-lg shadow-primary/5">
                        <CardHeader className="text-center space-y-4">
                            <div className="mx-auto bg-primary/10 w-12 h-12 rounded-full flex items-center justify-center">
                                <Sparkles className="w-6 h-6 text-primary" />
                            </div>
                            <div>
                                <CardTitle className="text-2xl font-bold bg-gradient-to-br from-primary to-primary-foreground bg-clip-text text-transparent">
                                    Welcome to the Waitlist
                                </CardTitle>
                                <CardDescription className="mt-2 text-base">
                                    You're one step away from accessing our exclusive features
                                </CardDescription>
                            </div>
                        </CardHeader>
                        <CardContent className="space-y-6">
                            <div className="space-y-4">
                                <div className="bg-muted/50 rounded-lg p-4 text-sm text-muted-foreground">
                                    <p>
                                        Your email <span className="font-medium text-foreground">{user?.primaryEmailAddress?.emailAddress}</span> is
                                        currently on our waitlist. Enter your invite code below to gain immediate access.
                                    </p>
                                </div>
                                {inviteError && (
                                    <div className="text-sm text-destructive bg-destructive/10 p-3 rounded-md">
                                        {inviteError}
                                    </div>
                                )}
                                <div className="space-y-3">
                                    <Input
                                        className="h-12 text-lg tracking-wider placeholder:text-muted-foreground/50"
                                        placeholder="Enter your invite code"
                                        value={value}
                                        onChange={onChange}
                                        disabled={isLoading}
                                    />
                                    <Button
                                        className="w-full h-12 text-base font-medium"
                                        onClick={onSubmit}
                                        disabled={isDisabled}
                                        size="lg"
                                    >
                                        {isLoading ? (
                                            <>
                                                <Loader2 className="h-5 w-5 animate-spin mr-2" />
                                                Verifying...
                                            </>
                                        ) : (
                                            'Unlock Access'
                                        )}
                                    </Button>
                                </div>
                            </div>
                        </CardContent>
                    </Card>
                </div>
            </div>
        </div>
    );
} 